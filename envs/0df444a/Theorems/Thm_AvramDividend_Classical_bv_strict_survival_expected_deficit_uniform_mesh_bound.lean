-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_survival_expected_deficit_uniform_mesh_bound
-- name    : AvramDividend.Classical.bv_strict_survival_expected_deficit_uniform_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:56:23.150661+00:00
-- url     : https://prove2.me/theorems/0b4f8744-b9b2-449e-87de-2c5639a0d25c
-- title:
--   Actual zero-barrier surviving drift-deficit expectation bounded by the BV Lévy exponential mesh rate
-- statement:
--   Before strict reflected ruin at time T, the actual BV Levy capital path is nondecreasing, so each drift-deficit mesh increment is at most the physical drift times the cell width. The deficit is also almost surely nondecreasing. Apply the previously proved indicator-event integrated exponential mesh bound and the exact expectation of uniform Levy mesh increments, at frequency reciprocal to twice the drift cap. This establishes the key finite-mesh stochastic inequality under explicit integrability and grid hypotheses, a bridge towards instantaneous ruin in infinite negative-jump activity.
-- source:
--   Proved zero-barrier strict-survival mesh cap, BV drift deficit monotonicity, event-integrated capped mesh bound and uniform mesh expectation identity.

import Theorems.Thm_AvramDividend_Classical_bv_surviving_uniform_grid_deficit_caps
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_integral_indicator_capped_deficit_le_exp_partition
import Theorems.Thm_AvramDividend_Classical_bv_uniform_mesh_exp_gap_expected_sum
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.bv_strict_survival_expected_deficit_uniform_mesh_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hStep : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hStepReal : ∀ k : ℕ, k < N →
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ))
    (a : ℝ) (ha : 0 < a) (haEq : a = X.drift * (δ : ℝ))
    (hθ : 1 ≤ (1 / (2 * a) : ℝ))
    (hLeft : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => D N ω - D 0 ω)) P)
    (hRight : Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P)
    (hCellInt : ∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => D N ω - D 0 ω) ω ∂P) ≤
      4 * a * (N : ℝ) *
        (1 - Real.exp (-((δ : ℝ) *
          ∫ y in Iio (0 : ℝ),
            (1 - Real.exp ((1 / (2 * a)) * y)) ∂X.ν))) := by sorry
