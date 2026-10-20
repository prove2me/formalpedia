-- Prove2me | Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_differentiableOn_dimension
-- name    : CohnElkies.lowerStripCappedGammaOuter_differentiableOn_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/5fac1529-937d-4ba4-8de2-5b4d7aafccab
-- title:
--   CohnElkies.lowerStripCappedGammaOuter_differentiableOn_dimension
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

theorem CohnElkies.lowerStripCappedGammaOuter_differentiableOn_dimension
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    DifferentiableOn ℂ
      (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by sorry
