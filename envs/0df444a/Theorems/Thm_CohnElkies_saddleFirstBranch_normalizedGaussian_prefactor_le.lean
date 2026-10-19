-- Prove2me | Theorems.Thm_CohnElkies_saddleFirstBranch_normalizedGaussian_prefactor_le
-- name    : CohnElkies.saddleFirstBranch_normalizedGaussian_prefactor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/9fd6eb1f-67a1-4b95-a774-f08bb670c356
-- title:
--   CohnElkies.saddleFirstBranch_normalizedGaussian_prefactor_le
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
open Filter Set MeasureTheory
open scoped Topology

theorem CohnElkies.saddleFirstBranch_normalizedGaussian_prefactor_le
    {ℓ V η c C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) *
        Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) ≤
      2 * Real.sqrt (Real.pi * C / c) := by sorry
