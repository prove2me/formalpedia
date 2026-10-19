-- Prove2me | Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs
-- name    : CohnElkies.integrable_abs_pow_mul_exp_neg_mul_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/e6e03d7e-6f1f-4810-a729-dae3cf8b60c6
-- title:
--   CohnElkies.integrable_abs_pow_mul_exp_neg_mul_abs
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

theorem CohnElkies.integrable_abs_pow_mul_exp_neg_mul_abs
    (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by sorry
