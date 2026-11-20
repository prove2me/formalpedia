-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
-- name    : AvramDividend.Classical.avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:51:24.594463+00:00
-- url     : https://prove2.me/theorems/646fef07-a6e7-473e-8082-4aee770e71ac
-- title:
--   Actual negative original controlled reserve at a physical clock bounds original ruin time above
-- statement:
--   For any original spectrally negative Lévy path under an actual dividend control, if the controlled riskProcess is strictly negative at a physical time σ, the actual original ruinTime, defined as the infimum of all times with negative controlled reserve, is no later than σ. This is a direct original source identity and bridges the proved finite-barrier physical Brownian–Poisson negative-jump event to the ruin-clipped horizon without asserting an invented stopping time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0) (hneg : riskProcess X x D σ ω < 0) :
    ruinTime X x D ω ≤ (σ : ℝ≥0∞) := by sorry
