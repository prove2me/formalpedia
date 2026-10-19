-- Prove2me | Theorems.Thm_CohnElkies_tendsto_lowerWallisComplexLogPhase_regularized
-- name    : CohnElkies.tendsto_lowerWallisComplexLogPhase_regularized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/141e7dc2-fceb-4d63-b2aa-3dfa5031cfe9
-- title:
--   CohnElkies.tendsto_lowerWallisComplexLogPhase_regularized
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

theorem CohnElkies.tendsto_lowerWallisComplexLogPhase_regularized (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        lowerWallisComplexLogPhase
          (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
            Complex.I * (u : ℂ)))
      atTop (𝓝 (1 + lowerEndpointPhase (2 * u))) := by sorry
