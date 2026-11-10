-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
-- name    : AvramDividend.Classical.avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:52:49.54126+00:00
-- url     : https://prove2.me/theorems/354411f0-28bf-480e-8a9b-66103716c0af
-- title:
--   Original bounded predictable negative-annulus physical grid compensated martingale L2 and zero mean
-- statement:
--   For any original right-continuous filtration-predictable bounded grid coefficients, the compensated actual negative-annulus marked jump count has an L2 finite-grid sum with expectation zero. The proof subtracts the two Proved original full negative-cutoff physical predictable-grid martingales, using source-exact real chronological count splitting and original Levy intensity splitting, without an auxiliary Poisson process. This is a genuinely random-coefficient finite-grid brick for the mixed infinite-activity stopped witness 5f12c023.
-- source:
--   Root-connected predictable random weight original annulus compensator; source Proved 06c6a15a fullcutoff stopped predictable L2, Proved 832d1bcb rate add, newly authored original window count additivity; consumer 5f12c023 original infinite stopped centered source then f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_real_window_count_additive
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (hnm : n ≤ m)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (k : ℕ) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1)))
      (-(1 / ((m : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      H i ω * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range k, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ Finset.range k, Z i ω ∂P) = 0 := by sorry
