-- Prove2me | Theorems.Thm_CohnElkies_radialMellinStrip_differentiableAt
-- name    : CohnElkies.radialMellinStrip_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/32b8081c-921f-46ae-a235-09ecdb58cc14
-- title:
--   CohnElkies.radialMellinStrip_differentiableAt
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
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

theorem CohnElkies.radialMellinStrip_differentiableAt {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (z : ℂ) (hz : -(d : ℝ) / 2 - 2 < z.im) :
    DifferentiableAt ℂ (radialMellinStrip hd f) z := by sorry
