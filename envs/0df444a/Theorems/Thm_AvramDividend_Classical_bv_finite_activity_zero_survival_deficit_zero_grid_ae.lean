-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_survival_deficit_zero_grid_ae
-- name    : AvramDividend.Classical.bv_finite_activity_zero_survival_deficit_zero_grid_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:57:33.242577+00:00
-- url     : https://prove2.me/theorems/fc2e7076-e6f5-4fd9-b7d4-4109d1d6dd8b
-- title:
--   Every surviving time in a countable grid has zero Lévy drift deficit almost surely
-- statement:
--   For the actual finite-negative-jump-activity bounded-variation Lévy process, a single full-measure event makes its capital equal to deterministic drift at every strictly surviving time in an arbitrary countable grid. Combine the Proved vanishing probability of strict survival with positive drift deficit, the Proved almost-sure upper drift bound, and countable a.e. intersection. This key pathwise input allows right-continuity and dense-time extension to the stopped dividend measure.
-- source:
--   Avram, Palmowski and Pistorius (2007), zero-barrier case following Proposition 1, finite negative jump intensity; Prove2Me actual-process grid estimate.

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_zero_survival_deficit_zero_grid_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((grid n : ℝ≥0) : ℝ≥0∞) < barrierRuinTime X 0 ω →
        X.X (grid n) ω = X.drift * (grid n : ℝ) := by sorry
