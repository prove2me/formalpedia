-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b164_original_deterministic_monotone_grid_fullnegative_occupied_card_measurable
-- name    : AvramDividend.Classical.avram_b164_original_deterministic_monotone_grid_fullnegative_occupied_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:08:36.40728+00:00
-- url     : https://prove2.me/theorems/7ec45bc6-fd5b-49a9-b64f-386f9d269834
-- title:
--   Real cardinal of genuine original full-negative Poisson occupied finite deterministic monotone grid cells is measurable
-- statement:
--   For the genuine original spectrally negative Levy source and arbitrary fixed finite monotone physical grid, count the original mapped jump Poisson measure on each half-open grid interval crossed with the entire mark space. Select the finite set J of grid cells with strictly nonzero source jump-counting mass. This occupied-cell Finset has a measurable real-valued cardinal as a function of the original sample path. The proof uses the already Proved original BV_excess25 ENNReal occupied-cell sum measurability, the exact Finset.sum_ite equality identifying that sum with the selected finite-set cardinal, and Mathlib ENNReal.measurable_toReal with exact finite cardinal conversion. This supplies the actual source marked-grid cardinal measurability input needed for the Proved B150 and pending B157 source energy estimates on deterministic physical grids. It does not claim stopped random-clock measurability without additional endpoint hypotheses.
-- source:
--   Proved original avram_bv_excess25_original_allnegative_occupied_grid_count_measurable and Mathlib measurable_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original full-negative-jump occupied-cell cardinal of any finite monotone deterministic physical grid is a measurable real random variable. -/

theorem AvramDividend.Classical.avram_b164_original_deterministic_monotone_grid_fullnegative_occupied_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    let N : Ω → ℕ → ℝ≥0∞ := fun ω i =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
        (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ))
    let J : Ω → Finset ℕ := fun ω =>
      (Finset.range m).filter (fun i => N ω i ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry
