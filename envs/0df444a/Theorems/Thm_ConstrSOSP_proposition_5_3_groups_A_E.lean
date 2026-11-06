-- Prove2me | Theorems.Thm_ConstrSOSP_proposition_5_3_groups_A_E
-- name    : ConstrSOSP.proposition_5_3_groups_A_E
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:16.212208+00:00
-- url     : https://prove2.me/theorems/4878d675-3ee1-49cd-939b-f966554c8d8a
-- title:
--   Proposition 5.3 (ii): Groups A–E satisfy a gradient or curvature criterion
-- statement:
--   Let $\epsilon_0=10^{-10}$ and $\sigma=-1/2$. Consider the representative polynomials of Table 3 with colour gaps in the domains (22):
--
--   1. Group A, values $(a+b-1,a+b,0,a)$, arrows UULR, $a\ge10^{40}$, $b\ge10^{40}$;
--   2. Group B, values $(b-1,b,0,a)$, arrows ULUR, $B>10^9$, $9995B\le a\le10000B$, $99B\le b\le101B$;
--   3. Group C, values $(0,a-2,a,a-1)$, arrows LRDR, $a\ge10^{20}$;
--   4. Group D, values $(0,a,-1,-2)$, arrows URUU, $a\ge10^{20}$;
--   5. Group E, values $(0,a-1,-1,a)$, arrows URUR, $a\ge10^{20}$.
--
--   **Theorem.** At every $(x,y)\in[0,1]^2$ each polynomial satisfies
--   $$
--   |\partial_xf|>\epsilon_0,\quad |\partial_yf|>\epsilon_0\quad\text{or}\quad \lambda_{\min}(\nabla^2f)<-\epsilon_0 .
--   $$
--
--   These transition groups may contain stationary points, but only ones with negative curvature, so they contain no $(\epsilon_0,\epsilon_0)$-SOSP.
--
--   Differences from the source:
--   - encoding: λ_min(∇²f) < −ϵ₀ → some unit vector v with vᵀ∇²f v < −ϵ₀; reason: equivalent by the Rayleigh quotient (25), p.36
--   - encoding: G_x, G_y, f_xx, f_xy, f_yy → iterated one-variable derivatives of the polynomial (deriv); reason: Lean convention; same values
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Proposition 5.3, p.33; Table 3, p.34; (22), p.35

import Mathlib
import Definitions.Def_ConstrSOSP_Dir
import Definitions.Def_ConstrSOSP_groupPoly
import Definitions.Def_ConstrSOSP_GradCrit
import Definitions.Def_ConstrSOSP_CurvCrit
import Definitions.Def_ConstrSOSP_eps0

namespace ConstrSOSP

/-- **Proposition 5.3, Groups A–E** (arXiv:2604.02285, 2 Nov 2026, Proposition 5.3, p.33:
"Consider … the representative polynomials … of Groups A–G with color gaps satisfying (22). …
for Groups A–G, σ = −1/2. At every point (x, y) ∈ [0, 1]^2, each of these polynomials satisfies
at least one of Gy criterion, Gx criterion, or λ criterion.").

With `σ = −1/2` and `ϵ₀ = 10⁻¹⁰`, at every `(x, y) ∈ [0, 1]²` the representative polynomial of
each group (corner values and arrows of Table 3, p.34) satisfies `|G_x| > ϵ₀`, `|G_y| > ϵ₀` or
`λ_min(∇²f) < −ϵ₀`, for all colour gaps in the domains (22), p.35:
1. Group A, values `(a + b − 1, a + b, 0, a)`, arrows UULR, when `a ≥ 10⁴⁰`, `b ≥ 10⁴⁰`;
2. Group B, values `(b − 1, b, 0, a)`, arrows ULUR, when `B > 10⁹`, `9995B ≤ a ≤ 10000B`,
   `99B ≤ b ≤ 101B`;
3. Group C, values `(0, a − 2, a, a − 1)`, arrows LRDR, when `a ≥ 10²⁰`;
4. Group D, values `(0, a, −1, −2)`, arrows URUU, when `a ≥ 10²⁰`;
5. Group E, values `(0, a − 1, −1, a)`, arrows URUR, when `a ≥ 10²⁰`. -/
theorem proposition_5_3_groups_A_E (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    (∀ a b : ℝ, 10 ^ 40 ≤ a → 10 ^ 40 ≤ b →
      GradCrit (groupPoly (-1 / 2) (a + b - 1) (a + b) 0 a Dir.up Dir.up Dir.left Dir.right)
          (eps0 : ℝ) x y ∨
        CurvCrit (groupPoly (-1 / 2) (a + b - 1) (a + b) 0 a Dir.up Dir.up Dir.left Dir.right)
          (eps0 : ℝ) x y) ∧
    (∀ B a b : ℝ, 10 ^ 9 < B → 9995 * B ≤ a → a ≤ 10000 * B → 99 * B ≤ b → b ≤ 101 * B →
      GradCrit (groupPoly (-1 / 2) (b - 1) b 0 a Dir.up Dir.left Dir.up Dir.right)
          (eps0 : ℝ) x y ∨
        CurvCrit (groupPoly (-1 / 2) (b - 1) b 0 a Dir.up Dir.left Dir.up Dir.right)
          (eps0 : ℝ) x y) ∧
    (∀ a : ℝ, 10 ^ 20 ≤ a →
      GradCrit (groupPoly (-1 / 2) 0 (a - 2) a (a - 1) Dir.left Dir.right Dir.down Dir.right)
          (eps0 : ℝ) x y ∨
        CurvCrit (groupPoly (-1 / 2) 0 (a - 2) a (a - 1) Dir.left Dir.right Dir.down Dir.right)
          (eps0 : ℝ) x y) ∧
    (∀ a : ℝ, 10 ^ 20 ≤ a →
      GradCrit (groupPoly (-1 / 2) 0 a (-1) (-2) Dir.up Dir.right Dir.up Dir.up) (eps0 : ℝ) x y ∨
        CurvCrit (groupPoly (-1 / 2) 0 a (-1) (-2) Dir.up Dir.right Dir.up Dir.up)
          (eps0 : ℝ) x y) ∧
    (∀ a : ℝ, 10 ^ 20 ≤ a →
      GradCrit (groupPoly (-1 / 2) 0 (a - 1) (-1) a Dir.up Dir.right Dir.up Dir.right)
          (eps0 : ℝ) x y ∨
        CurvCrit (groupPoly (-1 / 2) 0 (a - 1) (-1) a Dir.up Dir.right Dir.up Dir.right)
          (eps0 : ℝ) x y) := by sorry

end ConstrSOSP
