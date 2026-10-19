-- Prove2me | Theorems.Thm_CohnElkies_tendsto_integral_lowerWallisRegularizedPhaseKernel
-- name    : CohnElkies.tendsto_integral_lowerWallisRegularizedPhaseKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/eb0d993e-8f81-46ab-b50b-4286156b1ee2
-- title:
--   CohnElkies.tendsto_integral_lowerWallisRegularizedPhaseKernel
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

theorem CohnElkies.tendsto_integral_lowerWallisRegularizedPhaseKernel
    (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ t : ℝ in Ioi 0,
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t)
      atTop
      (𝓝 (∫ t : ℝ in Ioi 0, lowerWallisPhaseKernel u t)) := by sorry
