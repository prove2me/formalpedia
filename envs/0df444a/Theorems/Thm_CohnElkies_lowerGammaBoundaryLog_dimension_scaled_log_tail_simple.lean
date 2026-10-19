-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
-- name    : CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/baa80257-856f-4460-87d2-41e364486e90
-- title:
--   CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
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
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : 1 ≤ |Y|) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
        ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * Real.exp 1 * c ^ 2 / |Y|) := by sorry
