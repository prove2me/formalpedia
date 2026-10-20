-- Prove2me | Theorems.Thm_CohnElkies_strip_exp_abs_log_integrableOn_Ioi
-- name    : CohnElkies.strip_exp_abs_log_integrableOn_Ioi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/2e60332f-67a2-40cc-87ce-841bd9f5cbdd
-- title:
--   CohnElkies.strip_exp_abs_log_integrableOn_Ioi
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

theorem CohnElkies.strip_exp_abs_log_integrableOn_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => Real.exp ((-a) * x) * |Real.log x|)
      (Ioi (0 : ℝ)) := by sorry
