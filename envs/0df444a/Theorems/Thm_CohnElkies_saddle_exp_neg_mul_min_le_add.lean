-- Prove2me | Theorems.Thm_CohnElkies_saddle_exp_neg_mul_min_le_add
-- name    : CohnElkies.saddle_exp_neg_mul_min_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/e5d0055b-e598-4a17-b9dc-23f59991f7ab
-- title:
--   CohnElkies.saddle_exp_neg_mul_min_le_add
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
open Filter Set MeasureTheory
open scoped Topology

theorem CohnElkies.saddle_exp_neg_mul_min_le_add
    {a x y : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a * min x y) ≤
      Real.exp (-a * x) + Real.exp (-a * y) := by sorry
