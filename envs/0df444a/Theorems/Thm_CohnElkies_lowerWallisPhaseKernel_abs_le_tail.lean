-- Prove2me | Theorems.Thm_CohnElkies_lowerWallisPhaseKernel_abs_le_tail
-- name    : CohnElkies.lowerWallisPhaseKernel_abs_le_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/57c3ded3-789d-42ba-aacb-e085ddd946a7
-- title:
--   CohnElkies.lowerWallisPhaseKernel_abs_le_tail
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

theorem CohnElkies.lowerWallisPhaseKernel_abs_le_tail
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisPhaseKernel u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by sorry
