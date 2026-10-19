-- Prove2me | Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_scaled_convolution
-- name    : CohnElkies.lowerStripPoissonMajorant_scaled_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/5f054474-f495-4e1c-9a1a-2d9685395aeb
-- title:
--   CohnElkies.lowerStripPoissonMajorant_scaled_convolution
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

theorem CohnElkies.lowerStripPoissonMajorant_scaled_convolution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R σ s : ℝ) :
    lowerStripPoissonMajorant ℓ R σ s =
      ∫ Y : ℝ,
        stripPoissonKernel σ (s / ℓ - Y) *
          lowerGammaBoundaryLog ℓ R (ℓ * Y) := by sorry
