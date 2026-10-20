-- Prove2me | Theorems.Thm_CohnElkies_integral_lowerWallisRegularizedPhaseKernel
-- name    : CohnElkies.integral_lowerWallisRegularizedPhaseKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/8ef045b1-e3f8-40c9-a7f4-190d4adfc251
-- title:
--   CohnElkies.integral_lowerWallisRegularizedPhaseKernel
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
open Filter MeasureTheory Set
open scoped Interval Topology

theorem CohnElkies.integral_lowerWallisRegularizedPhaseKernel
    {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∫ t : ℝ in Ioi 0,
      lowerWallisRegularizedPhaseKernel a u t) =
      (1 + ((a : ℂ) - Complex.I * (u : ℂ)) *
        Complex.log ((a : ℂ) - Complex.I * (u : ℂ)) -
        (((a : ℂ) - Complex.I * (u : ℂ)) + 1) *
          Complex.log (((a : ℂ) - Complex.I * (u : ℂ)) + 1)).re := by sorry
