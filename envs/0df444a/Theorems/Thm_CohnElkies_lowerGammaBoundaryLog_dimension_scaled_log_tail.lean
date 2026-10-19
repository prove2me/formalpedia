-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail
-- name    : CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/954f532c-d419-4f17-a887-16d44f6f97a9
-- title:
--   CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail
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
open scoped FourierTransform Interval RealInnerProductSpace Topology

theorem CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail
    {d : ℕ} (hd : 0 < d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth
            (Real.pi * |((d : ℝ) / 2) * Y| / 2)) := by sorry
