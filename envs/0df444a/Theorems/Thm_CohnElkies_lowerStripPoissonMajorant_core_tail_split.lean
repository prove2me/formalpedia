-- Prove2me | Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_core_tail_split
-- name    : CohnElkies.lowerStripPoissonMajorant_core_tail_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/05ef3597-d6ad-482d-8b86-cea1010d5825
-- title:
--   CohnElkies.lowerStripPoissonMajorant_core_tail_split
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

theorem CohnElkies.lowerStripPoissonMajorant_core_tail_split
    {d : ℕ} (hd : 2 ≤ d) {c σ S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hS : 2 ≤ S) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
      (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
      (((d : ℝ) / 2) *
        Real.log ((8 * Real.pi * Real.exp 1 * c ^ 2) / S)) *
          stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by sorry
