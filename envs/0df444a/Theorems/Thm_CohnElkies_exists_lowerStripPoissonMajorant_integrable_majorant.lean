-- Prove2me | Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_integrable_majorant
-- name    : CohnElkies.exists_lowerStripPoissonMajorant_integrable_majorant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/ea39e1bc-7920-4d50-9871-2932fab2c12f
-- title:
--   CohnElkies.exists_lowerStripPoissonMajorant_integrable_majorant
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

theorem CohnElkies.exists_lowerStripPoissonMajorant_integrable_majorant
    {c : ℝ} (hc : 0 < c) (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ S : ℝ,
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2)
              (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
            C * Real.exp (-γ * ((d : ℝ) / 2)) /
              (1 + |S|) ^ 2 := by sorry
