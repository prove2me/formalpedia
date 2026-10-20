-- Prove2me | Theorems.Thm_CohnElkies_strip_exp_abs_integrable
-- name    : CohnElkies.strip_exp_abs_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/92068d7e-f916-4da5-ae66-39998599f6c0
-- title:
--   CohnElkies.strip_exp_abs_integrable
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

theorem CohnElkies.strip_exp_abs_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp ((-a) * |y|)) := by sorry
