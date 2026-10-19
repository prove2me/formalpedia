-- Prove2me | Theorems.Thm_CohnElkies_norm_halfIntegerGammaFactor
-- name    : CohnElkies.norm_halfIntegerGammaFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/012902f3-262a-4df1-8e07-4cf8d6dde7a6
-- title:
--   CohnElkies.norm_halfIntegerGammaFactor
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

theorem CohnElkies.norm_halfIntegerGammaFactor (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) := by sorry
