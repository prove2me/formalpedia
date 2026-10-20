-- Prove2me | Theorems.Thm_CohnElkies_integral_scaled_exp_change_Ioi
-- name    : CohnElkies.integral_scaled_exp_change_Ioi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/618b4714-35d1-4217-ad98-07fb7a1bfa85
-- title:
--   CohnElkies.integral_scaled_exp_change_Ioi
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
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem CohnElkies.integral_scaled_exp_change_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    (∫ r : ℝ in Ioi 0, f r) =
      ∫ v : ℝ, (R * Real.exp v) • f (R * Real.exp v) := by sorry
