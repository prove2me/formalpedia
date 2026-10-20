-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_antitoneOn
-- name    : CohnElkies.lowerGammaBoundaryCapped_dimension_antitoneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/5779630a-0b3a-4960-a624-0f9ac1978507
-- title:
--   CohnElkies.lowerGammaBoundaryCapped_dimension_antitoneOn
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

theorem CohnElkies.lowerGammaBoundaryCapped_dimension_antitoneOn
    {d : ℕ} (R D : ℝ) :
    AntitoneOn
      (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
      (Ici (0 : ℝ)) := by sorry
