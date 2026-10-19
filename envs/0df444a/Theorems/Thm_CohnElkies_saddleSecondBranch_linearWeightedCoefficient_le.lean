-- Prove2me | Theorems.Thm_CohnElkies_saddleSecondBranch_linearWeightedCoefficient_le
-- name    : CohnElkies.saddleSecondBranch_linearWeightedCoefficient_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/b42fdfc9-c1c5-4625-8740-e4c41ab15bf6
-- title:
--   CohnElkies.saddleSecondBranch_linearWeightedCoefficient_le
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
open Filter Set MeasureTheory intervalIntegral
open scoped Topology

theorem CohnElkies.saddleSecondBranch_linearWeightedCoefficient_le
    {a η C : ℝ}
    (ha : 0 < a)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / a ≤ C) :
    2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
        (2 / (a / 2)) ≤
      (8 * C * (1 + (6 * C) ^ 3)) * η ^ 4 := by sorry
