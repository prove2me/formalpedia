-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_discounted_HJB_generator_physical_strict_interior_finite_grid_sum_nonpositive
-- name    : AvramDividend.Classical.avram_b24_original_discounted_HJB_generator_physical_strict_interior_finite_grid_sum_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:50:41.506873+00:00
-- url     : https://prove2.me/theorems/a3d31258-0437-47f2-8ddf-cfe04a9118c0
-- title:
--   True original discounted negative-generator HJB residual has nonpositive finite physical stopped interior-grid sum
-- statement:
--   For the genuine original spectrally negative Lévy process X, any candidate C2 value w satisfying the original HJB generator inequality (X.generator w-qw)(y)≤0 at every positive strict reserve y under finite cap C, and any original finite physical mesh of ordered times s_i≤t_i with reserve points y_i strictly in (0,C), the summed discounted physical time-weighted HJB generator residual is nonpositive. Each coefficient exp(-q s_i) times the true nonnegative elapsed time is nonnegative and each actual generator residual is nonpositive, so the exact original finite real sum is nonpositive. This isolates the strictly interior compensator-drift SIGN component required in B219 physical stopped Ito-Meyer cash ledger without asserting the missing Gaussian/marked grid identity, right payments, ruin contact, or integrable L1 error.
-- source:
--   Original spectral-negative Lévy generator HJB inequality and finite nonpositive source drift sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_discounted_HJB_generator_physical_strict_interior_finite_grid_sum_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (y : ι → ℝ)
    (hTimes : ∀ i ∈ S, s i ≤ t i)
    (hInterior : ∀ i ∈ S,
      0 < y i ∧ ENNReal.ofReal (y i) < C) :
    (∑ i ∈ S, Real.exp (-(q * (s i : ℝ))) *
      ((t i : ℝ) - (s i : ℝ)) *
        (X.generator w (y i) - q * w (y i))) ≤ 0 := by sorry
