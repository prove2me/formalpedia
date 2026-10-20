-- Prove2me | Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_logarithmic_tail
-- name    : CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/b05ee53c-bd54-4fe1-aa8c-a5a2f32f6386
-- title:
--   CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail
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

theorem CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail
    {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ S : ℝ, B ≤ |S| →
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
              -κ * ((d : ℝ) / 2) * Real.log (|S| / A) := by sorry
