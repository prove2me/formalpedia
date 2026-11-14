-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b166_original_random_grid_negative_cutoff_occupied_card_measurable
-- name    : AvramDividend.Classical.avram_b166_original_random_grid_negative_cutoff_occupied_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:12:45.67926+00:00
-- url     : https://prove2.me/theorems/9e43f4e4-e441-493d-a3cd-0e1b649a2c8f
-- title:
--   Original random physical grid negative Poisson band occupied cell cardinal is measurable
-- statement:
--   For the original spectrally negative Levy process, choose a finite index set of potentially random source clock intervals with measurable left and right endpoints. For one reciprocal negative jump band cutoff, form the original marked Poisson source measure count on each physical interval and select all finite indices where that count is nonzero. The real-valued cardinal of the resulting original source occupied cell Finset is measurable. Proved jump_phys13 ensures each original random interval cutoff count is measurable. Each nonzero count event is measurable and its indicator is measurable; finite sums preserve measurability. The indicator sum equals the finite occupied cell cardinal. This provides a source-faithful measurable contact count for Gaussian and negative-jump finite-mesh Ito localisation, without requiring deterministic source endpoints or a second-moment assumption.
-- source:
--   Proved original jump_phys13 random source negative-band count measurable, Mathlib measurableSet preimage and Finset.measurable_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b166_original_random_grid_negative_cutoff_occupied_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut : ℕ) (S : Finset ℕ)
    (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i)) :
    let N : Ω → ℕ → ℝ≥0∞ := fun ω i =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => N ω i ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry
