-- Prove2me | Theorems.Thm_CohnElkies_poissonLogisticDensity_abs_moment_integrable
-- name    : CohnElkies.poissonLogisticDensity_abs_moment_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/92c46299-ba55-4eab-942d-d2c162e61e4e
-- title:
--   CohnElkies.poissonLogisticDensity_abs_moment_integrable
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

theorem CohnElkies.poissonLogisticDensity_abs_moment_integrable (n : ℕ) :
    Integrable
      (fun u : ℝ => poissonLogisticDensity u * |u| ^ n) := by sorry
