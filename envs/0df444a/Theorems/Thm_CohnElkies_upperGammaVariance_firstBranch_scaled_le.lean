-- Prove2me | Theorems.Thm_CohnElkies_upperGammaVariance_firstBranch_scaled_le
-- name    : CohnElkies.upperGammaVariance_firstBranch_scaled_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/920c32e5-2b9f-4119-8291-bcf782a59ab3
-- title:
--   CohnElkies.upperGammaVariance_firstBranch_scaled_le
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

theorem CohnElkies.upperGammaVariance_firstBranch_scaled_le
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hscale : 1 ≤ ℓ * η) :
    η * upperGammaVariance ℓ η ≤ (3 / 2 : ℝ) := by sorry
