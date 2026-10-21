-- Prove2me | Theorems.Thm_CrowdContest_Pooling_concave_deriv_inverse
-- name    : CrowdContest.Pooling.concave_deriv_inverse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:24.85199+00:00
-- url     : https://prove2.me/theorems/654a6654-1059-4e72-aa02-150e471993d5
-- title:
--   Proof of Proposition 1(ii)(b), OA p. 3 — if C′ is convex, then ½(C′⁻¹(y₁) + C′⁻¹(y₂)) ≤ C′⁻¹((y₁ + y₂)/2)
-- statement:
--   Let $C$ be a cost function (continuous on $[0,\infty)$, $C'>0$ and $C''>0$ on $(0,\infty)$) whose derivative $C'$ is convex on $(0,\infty)$. If $a,b,c>0$ satisfy
--   $$C'(c)=\frac{C'(a)+C'(b)}{2},$$
--   then $a+b\le 2c$.
--
--   With $y_1=C'(a)$ and $y_2=C'(b)$ this says $\tfrac12\big(C'^{-1}(y_1)+C'^{-1}(y_2)\big)\le C'^{-1}\big(\tfrac{y_1+y_2}{2}\big)$: the inverse of a convex increasing marginal cost is concave. It is the step that simplifies the condition of Proposition 1(ii) to $h^\circ>h/2$ when $C_1=C_2$.
--
--   **Formalization Note** The inverse function of the page is replaced by the equivalent inverse-free statement on points of $(0,\infty)$; "$y_1,y_2$ in the domain of $C'^{-1}$" is the requirement that they be values $C'(a)$, $C'(b)$, and the midpoint is assumed to be a value $C'(c)$.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), proof of Proposition 1, part (ii)(b), OA p. 3

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Proof of Proposition 1(ii)(b), OA p. 3: if the marginal cost `C'` is convex on `(0, ∞)`, its
inverse is concave, `½ (C'⁻¹(y₁) + C'⁻¹(y₂)) ≤ C'⁻¹((y₁ + y₂)/2)`. Inverse-free form: with
`y₁ = C'(a)`, `y₂ = C'(b)` and `C'(c) = (y₁ + y₂)/2`, `a + b ≤ 2c`. -/
theorem concave_deriv_inverse (C : ℝ → ℝ) (hC : IsCost C)
    (hconv : ConvexOn ℝ (Set.Ioi 0) (deriv C)) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : deriv C c = (deriv C a + deriv C b) / 2) :
    a + b ≤ 2 * c := by sorry

end CrowdContest.Pooling
