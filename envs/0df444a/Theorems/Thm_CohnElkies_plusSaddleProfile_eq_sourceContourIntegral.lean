-- Prove2me | Theorems.Thm_CohnElkies_plusSaddleProfile_eq_sourceContourIntegral
-- name    : CohnElkies.plusSaddleProfile_eq_sourceContourIntegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/35738557-bc20-4cb7-81e5-1f835536504c
-- title:
--   CohnElkies.plusSaddleProfile_eq_sourceContourIntegral
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

theorem CohnElkies.plusSaddleProfile_eq_sourceContourIntegral
    {ε ℓ r u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (hu : -1 < u) :
    plusSaddleProfile ε ℓ r =
      ((ℓ / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ T : ℝ,
          saddleMellinInversePower r
              (saddleSourceMellinContour ℓ u T) *
            plusSaddleMellinData ε ℓ
              (saddleSourceMellinContour ℓ u T)) := by sorry
