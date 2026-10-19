-- Prove2me | Theorems.Thm_CohnElkies_abs_exp_sub_one_le_abs_mul_exp_abs
-- name    : CohnElkies.abs_exp_sub_one_le_abs_mul_exp_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/4e37e5af-9355-4b41-8aca-97141d52c339
-- title:
--   CohnElkies.abs_exp_sub_one_le_abs_mul_exp_abs
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
open scoped Topology

theorem CohnElkies.abs_exp_sub_one_le_abs_mul_exp_abs (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by sorry
