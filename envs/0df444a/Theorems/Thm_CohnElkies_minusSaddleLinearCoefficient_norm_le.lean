-- Prove2me | Theorems.Thm_CohnElkies_minusSaddleLinearCoefficient_norm_le
-- name    : CohnElkies.minusSaddleLinearCoefficient_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/cde436c5-6bcd-4318-a99d-c18e3e6c1b5d
-- title:
--   CohnElkies.minusSaddleLinearCoefficient_norm_le
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

theorem CohnElkies.minusSaddleLinearCoefficient_norm_le (z : ℂ) :
    ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by sorry
