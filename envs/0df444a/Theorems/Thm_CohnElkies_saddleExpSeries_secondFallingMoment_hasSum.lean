-- Prove2me | Theorems.Thm_CohnElkies_saddleExpSeries_secondFallingMoment_hasSum
-- name    : CohnElkies.saddleExpSeries_secondFallingMoment_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/43d9b2fe-f668-4601-8fe8-f789470b3728
-- title:
--   CohnElkies.saddleExpSeries_secondFallingMoment_hasSum
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

theorem CohnElkies.saddleExpSeries_secondFallingMoment_hasSum (y : ℝ) :
    HasSum
      (fun n : ℕ =>
        (n : ℝ) * ((n : ℝ) - 1) *
          (y ^ n / (n.factorial : ℝ)))
      (y ^ 2 * Real.exp y) := by sorry
