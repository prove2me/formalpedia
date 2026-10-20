-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_norm
-- name    : CohnElkies.saddleSourceCenteredMinusIntegrand_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/4b372c84-5a2f-46a1-adaf-0b49745e1b77
-- title:
--   CohnElkies.saddleSourceCenteredMinusIntegrand_norm
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology

theorem CohnElkies.saddleSourceCenteredMinusIntegrand_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (v T : ℝ) :
    ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ := by sorry
