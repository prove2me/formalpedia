-- Prove2me | Theorems.Thm_CEPolytopeHard_interpolant_bounds
-- name    : CEPolytopeHard.interpolant_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:16:36.682334+00:00
-- url     : https://prove2.me/theorems/eee1cb09-02d1-4923-8a22-3ae54373bb63
-- title:
--   Interpolation property of $p_m$: $x^2 \le p_m(x) \le x^2 + 4^{-(m+1)}$
-- statement:
--   For every $m \in \mathbb N$:
--
--   1. $p_m$ agrees with $x^2$ on the mesh $2^{-m}\mathbb Z \cap [0,1]$: $p_m(j/2^m) = (j/2^m)^2$ for $0 \le j \le 2^m$;
--   2. on every mesh interval $[a, b] = [j/2^m, (j+1)/2^m]$, its error is
--   $$
--   p_m(x) - x^2 = (x - a)(b - x);
--   $$
--   3. hence, for every $x \in [0,1]$,
--   $$
--   x^2 \le p_m(x) \le x^2 + 4^{-(m+1)} .
--   $$
--
--   So $p_m$ is the piecewise-linear interpolation of $x^2$ on the dyadic mesh, and the polytope (13) represents an approximation of $x^2$ with $O(m)$ variables.
--
--   Differences from the source:
--   - encoding: "p_m linearly interpolates x² on the mesh" → p_m equals x² at the mesh points and p_m(x) − x² = (x − a)(b − x) on each mesh interval; reason: the error identity makes p_m affine on each mesh interval, which is the linear interpolation
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), p.21 (sentence after the definition of p_m; Figure 3)

import Mathlib
import Definitions.Def_CEPolytopeHard_pm

set_option autoImplicit false

namespace CEPolytopeHard

/-- **`p_m` interpolates `x²` on the dyadic mesh** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, p.21: "The function p_m linearly
interpolates x² on the mesh 2^{−m}Z ∩ [0, 1], as illustrated in Figure 3. On a mesh interval [a, b],
its error is (x − a)(b − x), so x² ≤ p_m(x) ≤ x² + 4^{−(m+1)}").

For every `m ∈ ℕ`:
1. `p_m(j/2^m) = (j/2^m)²` for every integer `0 ≤ j ≤ 2^m`;
2. on each mesh interval `[a, b] = [j/2^m, (j + 1)/2^m]`, `p_m(x) − x² = (x − a)(b − x)`;
3. `x² ≤ p_m(x) ≤ x² + 4^{−(m+1)}` for every `x ∈ [0, 1]`.

**Formalization Note** Clause 2 with `p_m − x²` quadratic says that `p_m` is affine on each mesh
interval, i.e. the linear interpolation of clause 1. -/
theorem interpolant_bounds (m : ℕ) :
    (∀ j : ℕ, j ≤ 2 ^ m → pm m ((j : ℝ) / 2 ^ m) = ((j : ℝ) / 2 ^ m) ^ 2) ∧
    (∀ j : ℕ, j < 2 ^ m → ∀ x ∈ Set.Icc ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m),
      pm m x - x ^ 2 = (x - (j : ℝ) / 2 ^ m) * (((j : ℝ) + 1) / 2 ^ m - x)) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ pm m x ∧ pm m x ≤ x ^ 2 + (4 : ℝ) ^ (-((m : ℤ) + 1)) := by sorry

end CEPolytopeHard
