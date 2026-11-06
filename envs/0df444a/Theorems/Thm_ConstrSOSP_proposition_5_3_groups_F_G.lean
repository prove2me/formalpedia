-- Prove2me | Theorems.Thm_ConstrSOSP_proposition_5_3_groups_F_G
-- name    : ConstrSOSP.proposition_5_3_groups_F_G
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:23.658206+00:00
-- url     : https://prove2.me/theorems/cb4a5776-9eae-4e66-96eb-2353e9e5fb94
-- title:
--   Proposition 5.3 (iii): Groups F–G satisfy a gradient criterion
-- statement:
--   Let $\epsilon_0=10^{-10}$, $\sigma=-1/2$ and $a\ge10^{20}$. Consider the representative polynomials of Table 3 of Group F (values $(0,1,a+1,a)$, arrows LLRD) and Group G (values $(0,a-1,-1,a)$, arrows UDUD).
--
--   **Theorem.** At every $(x,y)\in[0,1]^2$ both satisfy $|\partial_xf|>\epsilon_0$ or $|\partial_yf|>\epsilon_0$.
--
--   So Groups F and G contain no approximate first-order stationary point at all.
--
--   Differences from the source:
--   - encoding: G_x, G_y → one-variable derivatives of the polynomial (deriv); reason: Lean convention; same values
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Proposition 5.3, p.33; Table 3, p.34; (22), p.35

import Mathlib
import Definitions.Def_ConstrSOSP_Dir
import Definitions.Def_ConstrSOSP_groupPoly
import Definitions.Def_ConstrSOSP_GradCrit
import Definitions.Def_ConstrSOSP_eps0

namespace ConstrSOSP

/-- **Proposition 5.3, Groups F–G** (arXiv:2604.02285, 2 Nov 2026, Proposition 5.3, p.33:
"Groups 1–4 and F–G satisfy a gradient criterion at every point.").

With `σ = −1/2` and `ϵ₀ = 10⁻¹⁰`, at every `(x, y) ∈ [0, 1]²` the representative polynomials of
Group F (values `(0, 1, a + 1, a)`, arrows LLRD) and Group G (values `(0, a − 1, −1, a)`, arrows
UDUD; Table 3, p.34) satisfy `|G_x| > ϵ₀` or `|G_y| > ϵ₀`, whenever the colour gap is
`a ≥ 10²⁰` ((22), p.35). -/
theorem proposition_5_3_groups_F_G (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    (∀ a : ℝ, 10 ^ 20 ≤ a →
      GradCrit (groupPoly (-1 / 2) 0 1 (a + 1) a Dir.left Dir.left Dir.right Dir.down)
        (eps0 : ℝ) x y) ∧
    (∀ a : ℝ, 10 ^ 20 ≤ a →
      GradCrit (groupPoly (-1 / 2) 0 (a - 1) (-1) a Dir.up Dir.down Dir.up Dir.down)
        (eps0 : ℝ) x y) := by sorry

end ConstrSOSP
