-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_7
-- name    : DriftVarCtrl.FixedLB.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:23.720034+00:00
-- url     : https://prove2.me/theorems/4bb1dd2a-45e5-46c1-b020-fe4c3e577073
-- title:
--   Lemma 7, p. EC-13 — f₁(0, h₂) < 0 < f₁(U, h₂) on the (9)-interval
-- statement:
--   Assume $v_1 < v_2$ and let $h_2 \in (d_2^L\Delta h_1 + h_2^*,\ d_1^U\Delta h_1 + h_2^*)$. Then
--   $$f_1(0,h_2) < 0,\qquad f_1(U,h_2) > 0 .$$
--
--   By continuity, $f_1(\cdot,h_2)$ therefore has a root $S^* \in (0,U)$, the switching point of the optimal "1 then 2" policy.
--
--   **Formalization Note.** The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-13, Lemma 7, (88)–(89)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Lemma 7 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-13, (88)–(89)). With `h₁` fixed and `h₂ ∈ (dᴸ₂Δh₁ + h*₂, dᵁ₁Δh₁ + h*₂)`:
`f₁(0, h₂) < 0` and `f₁(U, h₂) > 0`.

Formalization Note: the standing `v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_7 (p : Params) (hv : v p .one < v p .two) (h₂' : ℝ)
    (h₂mem : h₂' ∈ Set.Ioo (dL2 p * Δh p .one + hstar p .two) (dU1 p * Δh p .one + hstar p .two)) :
    f1 p 0 h₂' < 0 ∧ 0 < f1 p p.U h₂' := by sorry

end DriftVarCtrl.FixedLB
