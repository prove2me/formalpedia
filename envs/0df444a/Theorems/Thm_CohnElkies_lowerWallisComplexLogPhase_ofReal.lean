-- Prove2me | Theorems.Thm_CohnElkies_lowerWallisComplexLogPhase_ofReal
-- name    : CohnElkies.lowerWallisComplexLogPhase_ofReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/88ae4259-40ca-4304-96d6-84a79e5d65bd
-- title:
--   CohnElkies.lowerWallisComplexLogPhase_ofReal
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

theorem CohnElkies.lowerWallisComplexLogPhase_ofReal
    {a : ℝ} (ha : 0 ≤ a) :
    lowerWallisComplexLogPhase (a : ℂ) =
      1 + a * Real.log a -
        (a + 1) * Real.log (a + 1) := by sorry
