-- Prove2me | Theorems.Thm_CohnElkies_radialProfile_neg
-- name    : CohnElkies.radialProfile_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/9f6db6e7-79bd-468b-8109-31782a1e40fc
-- title:
--   CohnElkies.radialProfile_neg
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
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem CohnElkies.radialProfile_neg {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (r : ℝ) :
    radialProfile hd f (-r) = radialProfile hd f r := by sorry
