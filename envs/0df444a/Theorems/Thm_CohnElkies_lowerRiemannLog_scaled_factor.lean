-- Prove2me | Theorems.Thm_CohnElkies_lowerRiemannLog_scaled_factor
-- name    : CohnElkies.lowerRiemannLog_scaled_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/2e16662a-494e-4e44-8977-5dc399db7b7f
-- title:
--   CohnElkies.lowerRiemannLog_scaled_factor
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

theorem CohnElkies.lowerRiemannLog_scaled_factor
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (j : ℝ) :
    Real.sqrt (j ^ 2 + (ℓ * T / 2) ^ 2) =
      ℓ * Real.sqrt ((j / ℓ) ^ 2 + T ^ 2 / 4) := by sorry
