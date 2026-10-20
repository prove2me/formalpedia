-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer
-- name    : CohnElkies.lowerGammaBoundaryLog_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/5f9ed4d3-95f0-4421-8bc0-bb042d7d6af3
-- title:
--   CohnElkies.lowerGammaBoundaryLog_integer
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

theorem CohnElkies.lowerGammaBoundaryLog_integer
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R y =
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by sorry
