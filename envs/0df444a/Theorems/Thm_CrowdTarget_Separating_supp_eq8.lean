-- Prove2me | Theorems.Thm_CrowdTarget_Separating_supp_eq8
-- name    : CrowdTarget.Separating.supp_eq8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:09.045783+00:00
-- url     : https://prove2.me/theorems/3ceabffc-a3ac-4e06-8e16-f2e499066b77
-- title:
--   Online Supplement (8): $p_1(C)<C/(\alpha\bar N)<p_2(C)$
-- statement:
--   Let $0<\alpha\le1$ and $C\ge S_H$. Then
--   $$
--   \Bigl|B-2\frac{C}{\bar N}\Bigr|<\sqrt{B^2+4\frac{C^2-2S_LC}{\bar N^2}},
--   $$
--   and consequently
--   $$
--   p_1(C)<\frac{C}{\alpha\bar N}<p_2(C),\qquad \frac{C}{\alpha\bar N}\ge\frac{C}{\bar N}.
--   $$
--
--   Together with the no-mimic window, this shows that among the designs on which the mimicking L-type can succeed, the binding constraint is $p\le p_2(C)$, and that the H-type can always succeed with positive probability on the curve $p=p_2(C)$.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, (8) (and p. 4)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, (8) (with the comparison used on Online Supplement p. 4).

For `0 < α ≤ 1` and every target `C ≥ S_H`,
`|B − 2C/N̄| < √(B² + 4(C² − 2 S_L C)/N̄²)`, and hence `p₁(C) < C/(αN̄) < p₂(C)` and
`C/(αN̄) ≥ C/N̄`. -/
theorem supp_eq8 (P : Params) (hP : P.Standing) (α C : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : P.SH ≤ C) :
    |B P - 2 * (C / P.Nbar)| <
        Real.sqrt (B P ^ 2 + 4 * ((C ^ 2 - 2 * P.SL * C) / P.Nbar ^ 2)) ∧
      p1 P α C < C / (α * P.Nbar) ∧ C / (α * P.Nbar) < p2 P α C ∧
      C / P.Nbar ≤ C / (α * P.Nbar) := by sorry

end CrowdTarget.Separating
