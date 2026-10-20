-- Prove2me | Theorems.Thm_CohnElkies_saddleExpSeries_term_le_exp_mul_half_pow
-- name    : CohnElkies.saddleExpSeries_term_le_exp_mul_half_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/c49e5cc4-c82c-48e2-a298-62018b8de1ac
-- title:
--   CohnElkies.saddleExpSeries_term_le_exp_mul_half_pow
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

theorem CohnElkies.saddleExpSeries_term_le_exp_mul_half_pow
    {y : ℝ} (hy : 0 ≤ y) (m : ℕ) :
    y ^ m / (m.factorial : ℝ) ≤
      Real.exp (2 * y) * (1 / 2 : ℝ) ^ m := by sorry
