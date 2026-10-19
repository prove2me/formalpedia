-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_pole_decomposition
-- name    : CohnElkies.lowerGammaBoundaryLog_pole_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/4c33f3df-e60b-4ac0-ac99-91c0b4a84c8a
-- title:
--   CohnElkies.lowerGammaBoundaryLog_pole_decomposition
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

theorem CohnElkies.lowerGammaBoundaryLog_pole_decomposition
    (ℓ R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ℓ R y =
      ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma
          (1 - Complex.I * (y : ℂ) / 2)‖ -
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖ -
        Real.log (|y| / 2) := by sorry
