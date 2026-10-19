-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceCenteredPlusIntegrand_sourcePointwise
-- name    : CohnElkies.saddleSourceCenteredPlusIntegrand_sourcePointwise
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/453353f6-b511-47bd-a7a8-0dd1ac39d07e
-- title:
--   CohnElkies.saddleSourceCenteredPlusIntegrand_sourcePointwise
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

theorem CohnElkies.saddleSourceCenteredPlusIntegrand_sourcePointwise
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ) (hu : -1 < u)
    (v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) *
      plusSaddleMellinData ε ℓ
        (saddleSourceMellinContour ℓ u T) =
    ((Real.exp (-(ℓ * (1 + u) * v)) *
        saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
      saddleSourceCenteredPlusIntegrand ε ℓ u v T := by sorry
