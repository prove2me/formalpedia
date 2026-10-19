-- Prove2me | Theorems.Thm_CohnElkies_lowerWallisRegularizedPhaseKernel_abs_le_moment
-- name    : CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_moment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/a73827c8-26c2-4e99-97a1-37d458dd32e6
-- title:
--   CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_moment
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

theorem CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_moment
    {a : ℝ} (hazero : 0 ≤ a) (haone : a ≤ 1)
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤ |u| + 2 := by sorry
