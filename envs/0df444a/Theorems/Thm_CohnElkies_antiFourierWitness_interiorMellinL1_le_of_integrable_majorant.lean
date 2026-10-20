-- Prove2me | Theorems.Thm_CohnElkies_antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
-- name    : CohnElkies.antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/eeaec21b-7702-491c-8366-82af9bbe179a
-- title:
--   CohnElkies.antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
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

theorem CohnElkies.antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
    {d : ℕ} (hd : 0 < d) {R σ γ C : ℝ}
    (hR : 0 < R) (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hpoint : ∀ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s))
    (hmajor : ∀ S : ℝ,
      Real.exp
        (lowerStripPoissonMajorant ((d : ℝ) / 2)
          R σ (((d : ℝ) / 2) * S)) ≤
        C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2) :
    (∫ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) ≤
      (C * lowerInverseQuadraticMass) *
        ((d : ℝ) / 2) * Real.exp (-γ * ((d : ℝ) / 2)) := by sorry
