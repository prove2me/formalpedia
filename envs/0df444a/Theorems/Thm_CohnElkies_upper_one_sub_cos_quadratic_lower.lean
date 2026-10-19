-- Prove2me | Theorems.Thm_CohnElkies_upper_one_sub_cos_quadratic_lower
-- name    : CohnElkies.upper_one_sub_cos_quadratic_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/c1b402fa-9771-4f2f-a267-ed8325171655
-- title:
--   CohnElkies.upper_one_sub_cos_quadratic_lower
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

theorem CohnElkies.upper_one_sub_cos_quadratic_lower
    {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 / 4 ≤ 1 - Real.cos x := by sorry
