-- Prove2me | Theorems.Thm_CrowdTarget_Separating_supp_case2_root
-- name    : CrowdTarget.Separating.supp_case2_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:08.688706+00:00
-- url     : https://prove2.me/theorems/66ce093e-726d-4646-ae2b-baad9b2cc0f4
-- title:
--   Case 2: $C^*(\alpha)$ solves $p_2(C^*)=v_H$
-- statement:
--   Let $\alpha^*<\alpha\le1$. Then the radicand $S_L^2+\bar N^2(\alpha^2v_H^2-\alpha v_HB)$ is nonnegative, so that
--   $$
--   C^*=S_L+\sqrt{S_L^2+\bar N^2(\alpha^2v_H^2-\alpha v_HB)}
--   $$
--   is well defined; moreover $C^*>S_H$, $p_2(C^*)=v_H$, and $C^*$ is the only target $C\ge S_H$ with $p_2(C)=v_H$.
--
--   This identifies the target at which the H-type's full-information price $v_H$ exactly deters mimicking.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, Case 2

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 5, Case 2.

For `α∗ < α ≤ 1` the radicand in (5) is nonnegative, `C∗(α) > S_H`, `p₂(C∗(α)) = v_H`, and
`C∗(α)` is the only target `C ≥ S_H` with `p₂(C) = v_H`. -/
theorem supp_case2_root (P : Params) (hP : P.Standing) (α : ℝ) (hα : alphaStar P < α)
    (hα1 : α ≤ 1) :
    0 ≤ P.SL ^ 2 + P.Nbar ^ 2 * (α ^ 2 * P.vH ^ 2 - α * P.vH * B P) ∧
      P.SH < Cstar P α ∧ p2 P α (Cstar P α) = P.vH ∧
      ∀ C : ℝ, P.SH ≤ C → p2 P α C = P.vH → C = Cstar P α := by sorry

end CrowdTarget.Separating
