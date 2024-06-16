const std = @import("std");

const Modulus = std.crypto.ff.Modulus;
const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;

const M = Modulus(4);
const ORDER: usize = 11;

const Point = struct { x: M.Fe, y: M.Fe };

/// Get random non-zero coefficients to represent a polynomial of degree `len`.
fn pick_random_coefficients(m: M, coefficients: *ArrayList(M.Fe), len: usize) !void {
    var prng = std.rand.DefaultPrng.init(0);

    for (0..len) |_| {
        const coeff = prng.random().intRangeAtMost(u4, 1, ORDER - 1);
        try coefficients.append(try M.Fe.fromPrimitive(u4, m, coeff));
    }
}

pub fn eval_poly(m: M, secret: M.Fe, coefficients: ArrayList(M.Fe), x: M.Fe) M.Fe {
    var accum = secret;
    var x_inner = x;

    for (coefficients.items) |c| {
        accum = m.add(accum, m.mul(
            c,
            x_inner,
        ));
        x_inner = m.mul(x_inner, x_inner);
    }

    return accum;
}

/// Secret sharing amongst `n` parties reconstructible from `t+1` parties.
///
/// Any set of `t` or fewer shares contain no information on `secret`.
/// whereas `secret` can be easily reconstructed from any `t+1` or more shares.
/// These are proven using Lagrange interpolation.
pub fn secret_sharing(allocator: Allocator, secret: M.Fe, t: usize, n: usize) !ArrayList(Point) {
    std.debug.assert(t <= n);
    std.debug.assert(t > 1);

    const m = try M.fromPrimitive(u4, ORDER);
    var coefficients = try ArrayList(M.Fe).initCapacity(allocator, t);
    defer coefficients.deinit();

    try pick_random_coefficients(m, &coefficients, t);

    var shares = try ArrayList(Point).initCapacity(allocator, n);

    // Compute shares for `n` parties
    for (0..n) |i| {
        const i_ff = try M.Fe.fromPrimitive(u4, m, @intCast(i));
        // Computing a share is simply evaluating the polynomial at
        // a point `i` (in the field)
        const evaled = eval_poly(
            m,
            secret,
            coefficients,
            i_ff,
        );

        // Form the shares
        try shares.append(Point{
            .x = i_ff,
            .y = evaled,
        });
    }

    return shares;
}

fn extended_gcd(a_: u4, b_: u4) !u4 {
    var x: u4 = 0;
    var last_x: u4 = 1;
    var y: u4 = 1;
    var last_y: u4 = 0;

    var a = a_;
    var b = b_;
    while (b != 0) {
        const quot = try std.math.divFloor(u4, a, b);

        a = b;
        b = a % b;
        x = last_x - quot * x;
        last_x = x;
        y = last_y - quot * y;
        last_y = y;
    }

    return last_x;
}

fn inverse(den: M.Fe, p: u4) !u4 {
    return try extended_gcd(try den.toPrimitive(u4), p);
}

fn lagrange_basis_at_zero(m: M, i: usize, shares: []Point) !M.Fe {
    var accum = try M.Fe.fromPrimitive(u4, m, 1);

    // Form the lagrange basis polynomial:
    //
    // $$
    // delta_i(x) = \prod_{j \in C}^{j \neq i}\frac{(x - j)}{(i - j)}
    // $$
    //
    // where C = set of shares as input to `reconstruct_secret`
    for (shares, 0..) |p, j| {
        // Lagrange polynomial has no basis polynomial at i == j
        if (i == j) continue;

        const zero = try M.Fe.fromPrimitive(u4, m, 0);

        // Why zero?
        // numerator = X - j = 0 - p.x
        const numerator = m.sub(zero, p.x);
        // denominator = i - j
        const denominator = m.sub(shares[i].x, p.x);

        // Find inverse and do numerator * denom_inverse, since we're working
        // in fields.
        const multiplicant = m.mul(
            numerator,
            try M.Fe.fromPrimitive(u4, m, try inverse(denominator, ORDER)),
        );
        accum = m.mul(accum, multiplicant);
    }
    return accum;
}

/// Reconstruct f(0) (which is the `secret`) by finding the summation of all f(i)delta_i(0), where f(i) is the i-th share.
///
/// $$
/// f(0) = \sum_{i \in C}^{}{f(i)\delta_i(0)}
/// $$
///
/// where C = `shares`
pub fn reconstruct_secret(m: M, shares: []Point) !M.Fe {
    var accum = try M.Fe.fromPrimitive(u4, m, 0);
    for (shares, 0..) |s, i| {
        const term = m.mul(s.y, try lagrange_basis_at_zero(m, i, shares));
        accum = m.add(accum, term);
    }

    return accum;
}

test "mpc: reconstructing passes" {
    const allocator = std.testing.allocator;
    const m = try M.fromPrimitive(u4, ORDER);

    const secret = try M.Fe.fromPrimitive(u4, m, 7);
    const t = 2; // 2 corruptible parties
    const n = 5; // 5 shares among 5 parties

    var shares = try secret_sharing(allocator, secret, t, n);
    defer shares.deinit();

    var prng = std.rand.DefaultPrng.init(0);

    // Try recovering secret with `t`+ 1 points.
    for (0..(n - (t + 1))) |_| {
        const idx = prng.random().intRangeAtMost(usize, 0, shares.items.len - 1);
        _ = shares.orderedRemove(idx);
    }

    const reconstructed = try reconstruct_secret(m, shares.items);
    try std.testing.expectEqual(secret, reconstructed);
}

test "mpc: fails below threshold" {
    const allocator = std.testing.allocator;
    const m = try M.fromPrimitive(u4, ORDER);

    const secret = try M.Fe.fromPrimitive(u4, m, 7);
    const t = 2; // 2 corruptible parties
    const n = 5; // 5 shares among 5 parties

    var shares = try secret_sharing(allocator, secret, t, n);
    defer shares.deinit();

    var prng = std.rand.DefaultPrng.init(0);

    // Try recovering secret with only `t` points. This should fail later!
    for (0..(n - t)) |_| {
        const idx = prng.random().intRangeAtMost(usize, 0, shares.items.len - 1);
        _ = shares.orderedRemove(idx);
    }

    const reconstructed = try reconstruct_secret(m, shares.items);
    try std.testing.expect(!secret.eql(reconstructed));
}
