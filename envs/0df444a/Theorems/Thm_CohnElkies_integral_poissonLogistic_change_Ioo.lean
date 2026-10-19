-- Prove2me | Theorems.Thm_CohnElkies_integral_poissonLogistic_change_Ioo
-- name    : CohnElkies.integral_poissonLogistic_change_Ioo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/c850972e-1637-446f-a4a0-ddd0ee885792
-- title:
--   CohnElkies.integral_poissonLogistic_change_Ioo
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

theorem CohnElkies.integral_poissonLogistic_change_Ioo {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x : ℝ in Ioo 0 1, f x) =
      ∫ u : ℝ, poissonLogisticDensity u •
        f (poissonLogistic u) := by sorry
