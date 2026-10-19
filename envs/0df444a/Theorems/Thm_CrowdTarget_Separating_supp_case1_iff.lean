-- Prove2me | Theorems.Thm_CrowdTarget_Separating_supp_case1_iff
-- name    : CrowdTarget.Separating.supp_case1_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:06.379218+00:00
-- url     : https://prove2.me/theorems/ddc081b4-f9b5-4a46-b80d-b265bdb76522
-- title:
--   Case 1: costless separation iff $\alpha\le\alpha^*$
-- statement:
--   Let $0<\alpha\le1$. Then
--   $$
--   v_H\le p_2(S_H)\iff\alpha\le\alpha^*,
--   $$
--   and when $\alpha\le\alpha^*$ the L-type earns no more by mimicking the H-type's complete-information design $(S_H,v_H)$ than at $(S_L,v_L)$. Hence for $\alpha\le\alpha^*$ the H-type separates at no cost.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 4, Case 1 (with (3))

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), Online Supplement p. 4, Case 1.

For `0 < α ≤ 1`: `v_H ≤ p₂(S_H)` holds exactly when `α ≤ α∗` (α∗ of (3)), and in that case the
L-type does not gain by mimicking the design `(S_H, v_H)`, so the H-type can separate at her
complete-information design (costless separation). -/
theorem supp_case1_iff (P : Params) (hP : P.Standing) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (P.vH ≤ p2 P α P.SH ↔ α ≤ alphaStar P) ∧
    (α ≤ alphaStar P →
      profit P α .L .H ⟨P.SH, P.vH⟩ ≤ profit P α .L .L ⟨P.SL, P.vL⟩) := by sorry

end CrowdTarget.Separating
