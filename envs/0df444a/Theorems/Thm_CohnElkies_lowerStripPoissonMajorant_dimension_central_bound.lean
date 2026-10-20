-- Prove2me | Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_dimension_central_bound
-- name    : CohnElkies.lowerStripPoissonMajorant_dimension_central_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/c75d5359-a141-401e-9205-0c9a44287904
-- title:
--   CohnElkies.lowerStripPoissonMajorant_dimension_central_bound
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

theorem CohnElkies.lowerStripPoissonMajorant_dimension_central_bound
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c) (hzero : 0 ≤ σ) (habove : σ < 1) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 ≤
      ((d : ℝ) / 2) * stripBottomMass σ *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ) +
        lowerRiemannPoissonError σ := by sorry
