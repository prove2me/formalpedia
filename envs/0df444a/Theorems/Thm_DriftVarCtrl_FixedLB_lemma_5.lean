-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_5
-- name    : DriftVarCtrl.FixedLB.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:16.747399+00:00
-- url     : https://prove2.me/theorems/d5de031f-83de-47fc-a81e-2ef19e8ab9cf
-- title:
--   Lemma 5, p. EC-9 — f₁(0, dᴸ₂Δh₁ + h*₂) = 0 and f₁(U, dᵁ₁Δh₁ + h*₂) = 0
-- statement:
--   Assume $v_1 < v_2$ and fix the model (in particular $h_1$). Then
--   $$f_1\big(0,\ d_2^L\Delta h_1 + h_2^*\big) = 0,\qquad f_1\big(U,\ d_1^U\Delta h_1 + h_2^*\big) = 0 .$$
--
--   The two values of $h_2$ are the endpoints of the $h_2$-interval of condition (9); at them the switching point of the "1 then 2" policy degenerates to $0$ or to $U$.
--
--   **Formalization Note.** The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-9, Lemma 5

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Lemma 5 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-9). With `h₁` fixed, `f₁(0, dᴸ₂Δh₁ + h*₂) = 0` and `f₁(U, dᵁ₁Δh₁ + h*₂) = 0`.

Formalization Note: the standing `v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_5 (p : Params) (hv : v p .one < v p .two) :
    f1 p 0 (dL2 p * Δh p .one + hstar p .two) = 0 ∧
    f1 p p.U (dU1 p * Δh p .one + hstar p .two) = 0 := by sorry

end DriftVarCtrl.FixedLB
