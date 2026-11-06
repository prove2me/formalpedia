-- Prove2me | Theorems.Thm_ConstrSOSP_proposition_5_3_groups_1_4
-- name    : ConstrSOSP.proposition_5_3_groups_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:15.099269+00:00
-- url     : https://prove2.me/theorems/5e4fbac8-fc0c-46ff-9c63-18e948074826
-- title:
--   Proposition 5.3 (i): Groups 1–4 satisfy a gradient criterion for $\sigma\in[-1/2,1/2]$
-- statement:
--   Let $\epsilon_0=10^{-10}$ and $\sigma\in[-1/2,1/2]$. For the corner values $(z_{00},z_{10},z_{01},z_{11})=(c,d,a,b)$ consider the representative polynomials of Table 3:
--
--   1. Group 1, arrows RRRR, with $c-d\ge1$, $a-b\ge1$;
--   2. Group 2, arrows UURR, with $c-d\ge-1$, $a-b\ge1$, $c-a\ge1$, $d-b\ge1$;
--   3. Group 3, arrows UURU, with the same inequalities as Group 2;
--   4. Group 4, arrows RUUU, with $c-d\ge1$, $a-b\ge-1$, $c-a\ge1$, $d-b\ge1$.
--
--   **Theorem.** At every $(x,y)\in[0,1]^2$ each of them satisfies
--   $$
--   |\partial_xf|>\epsilon_0\quad\text{or}\quad|\partial_yf|>\epsilon_0 .
--   $$
--
--   The standard groups therefore contain no $\epsilon_0$-approximate first-order stationary point, uniformly in $\sigma$ (negation of the corner data flips $\sigma$).
--
--   Differences from the source:
--   - encoding: G_x, G_y → one-variable derivatives of the polynomial (deriv); reason: Lean convention; same values
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Proposition 5.3, p.33; Table 3, p.34; (24), p.36

import Mathlib
import Definitions.Def_ConstrSOSP_Dir
import Definitions.Def_ConstrSOSP_groupPoly
import Definitions.Def_ConstrSOSP_GradCrit
import Definitions.Def_ConstrSOSP_eps0

namespace ConstrSOSP

/-- **Proposition 5.3, Groups 1–4** (arXiv:2604.02285, 2 Nov 2026, Proposition 5.3, p.33:
"Consider the representative polynomials of Groups 1–4 with corner values satisfying (24) … For
Groups 1–4, the claim holds uniformly for σ ∈ [−1/2, 1/2] … At every point (x, y) ∈ [0, 1]^2,
each of these polynomials satisfies at least one of Gy criterion, Gx criterion, or λ criterion.
Groups 1–4 and F–G satisfy a gradient criterion at every point.").

With `ϵ₀ = 10⁻¹⁰`, for every `σ ∈ [−1/2, 1/2]`, corner values `(z₀₀, z₁₀, z₀₁, z₁₁) = (c, d, a, b)`
(Table 3, p.34) and every `(x, y) ∈ [0, 1]²`, the representative polynomial satisfies a gradient
criterion `|G_x| > ϵ₀` or `|G_y| > ϵ₀`:
1. Group 1, arrows RRRR, when `c − d ≥ 1`, `a − b ≥ 1`;
2. Group 2, arrows UURR, and
3. Group 3, arrows UURU, when `c − d ≥ −1`, `a − b ≥ 1`, `c − a ≥ 1`, `d − b ≥ 1`;
4. Group 4, arrows RUUU, when `c − d ≥ 1`, `a − b ≥ −1`, `c − a ≥ 1`, `d − b ≥ 1`
(the inequalities (24), p.36). -/
theorem proposition_5_3_groups_1_4 (σ : ℝ) (hσ : -1 / 2 ≤ σ ∧ σ ≤ 1 / 2) (a b c d : ℝ)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    (1 ≤ c - d → 1 ≤ a - b →
      GradCrit (groupPoly σ c d a b Dir.right Dir.right Dir.right Dir.right) (eps0 : ℝ) x y) ∧
    (-1 ≤ c - d → 1 ≤ a - b → 1 ≤ c - a → 1 ≤ d - b →
      GradCrit (groupPoly σ c d a b Dir.up Dir.up Dir.right Dir.right) (eps0 : ℝ) x y) ∧
    (-1 ≤ c - d → 1 ≤ a - b → 1 ≤ c - a → 1 ≤ d - b →
      GradCrit (groupPoly σ c d a b Dir.up Dir.up Dir.right Dir.up) (eps0 : ℝ) x y) ∧
    (1 ≤ c - d → -1 ≤ a - b → 1 ≤ c - a → 1 ≤ d - b →
      GradCrit (groupPoly σ c d a b Dir.right Dir.up Dir.up Dir.up) (eps0 : ℝ) x y) := by sorry

end ConstrSOSP
