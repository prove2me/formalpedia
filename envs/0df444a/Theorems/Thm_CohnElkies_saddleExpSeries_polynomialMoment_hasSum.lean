-- Prove2me | Theorems.Thm_CohnElkies_saddleExpSeries_polynomialMoment_hasSum
-- name    : CohnElkies.saddleExpSeries_polynomialMoment_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/88ab7fb1-38f7-44a9-b466-d71a48800a87
-- title:
--   CohnElkies.saddleExpSeries_polynomialMoment_hasSum
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

theorem CohnElkies.saddleExpSeries_polynomialMoment_hasSum (y : ℝ) :
    HasSum
      (fun n : ℕ =>
        ((n : ℝ) + (n : ℝ) ^ 2) *
          (y ^ n / (n.factorial : ℝ)))
      ((2 * y + y ^ 2) * Real.exp y) := by sorry
