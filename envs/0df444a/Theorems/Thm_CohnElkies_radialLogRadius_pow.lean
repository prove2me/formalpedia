-- Prove2me | Theorems.Thm_CohnElkies_radialLogRadius_pow
-- name    : CohnElkies.radialLogRadius_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/4316df0f-99c4-4408-9b2e-978b0b97ebca
-- title:
--   CohnElkies.radialLogRadius_pow
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

theorem CohnElkies.radialLogRadius_pow {d : ℕ} (hd : 0 < d) (r : ℝ) :
    r ^ d = r * r ^ (d - 1) := by sorry
