-- Prove2me | Theorems.Thm_CohnElkies_normalizedCostSet_bddBelow
-- name    : CohnElkies.normalizedCostSet_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/040a5d5d-503f-4c2b-b957-1a9b57adc336
-- title:
--   CohnElkies.normalizedCostSet_bddBelow
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
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap

theorem CohnElkies.normalizedCostSet_bddBelow (d : ℕ) :
    BddBelow (Set.range (normalizedCost (d := d))) := by sorry
