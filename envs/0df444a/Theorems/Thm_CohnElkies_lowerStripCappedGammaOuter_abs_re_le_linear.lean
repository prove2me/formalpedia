-- Prove2me | Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_abs_re_le_linear
-- name    : CohnElkies.lowerStripCappedGammaOuter_abs_re_le_linear
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/7d428691-7a88-487f-bdff-a357518f97f0
-- title:
--   CohnElkies.lowerStripCappedGammaOuter_abs_re_le_linear
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

theorem CohnElkies.lowerStripCappedGammaOuter_abs_re_le_linear
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ,
        z ∈ Complex.im ⁻¹'
          Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
        |(lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re| ≤
          B * (1 + |z.re|) := by sorry
