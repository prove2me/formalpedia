-- Prove2me | Theorems.Thm_CohnElkies_upper_inv_one_sub_exp_neg_bounds
-- name    : CohnElkies.upper_inv_one_sub_exp_neg_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/0f7a4673-2c47-447a-95a0-fadd3dae8e6c
-- title:
--   CohnElkies.upper_inv_one_sub_exp_neg_bounds
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

theorem CohnElkies.upper_inv_one_sub_exp_neg_bounds
    {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ (1 - Real.exp (-x))⁻¹ ∧
      (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by sorry
