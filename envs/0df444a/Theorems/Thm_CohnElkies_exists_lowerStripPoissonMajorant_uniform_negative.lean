-- Prove2me | Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_uniform_negative
-- name    : CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/3a944db0-3ea0-4041-ae1b-1d032ac97e83
-- title:
--   CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative
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

theorem CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ s : ℝ,
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ s ≤
              -γ * ((d : ℝ) / 2) := by sorry
