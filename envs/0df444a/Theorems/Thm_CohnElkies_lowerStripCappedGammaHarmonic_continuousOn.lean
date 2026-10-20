-- Prove2me | Theorems.Thm_CohnElkies_lowerStripCappedGammaHarmonic_continuousOn
-- name    : CohnElkies.lowerStripCappedGammaHarmonic_continuousOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/ac25416f-b2a7-486f-83e6-a907cb8e4e4f
-- title:
--   CohnElkies.lowerStripCappedGammaHarmonic_continuousOn
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
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem CohnElkies.lowerStripCappedGammaHarmonic_continuousOn
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ContinuousOn (lowerStripCappedGammaHarmonic d R D)
      (Complex.im ⁻¹'
        Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by sorry
