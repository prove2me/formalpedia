-- Prove2me | Theorems.Thm_CohnElkies_integral_stripPoissonKernel_mul_lowerEndpointPhase
-- name    : CohnElkies.integral_stripPoissonKernel_mul_lowerEndpointPhase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/c447ab83-25cf-48c0-896b-8a020054fbb0
-- title:
--   CohnElkies.integral_stripPoissonKernel_mul_lowerEndpointPhase
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
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.integral_stripPoissonKernel_mul_lowerEndpointPhase
    {σ : ℝ} (habove : σ < 1) :
    (∫ T : ℝ, stripPoissonKernel σ T * lowerEndpointPhase T) =
      stripBottomMass σ * lowerPoissonEndpointExpectation σ := by sorry
