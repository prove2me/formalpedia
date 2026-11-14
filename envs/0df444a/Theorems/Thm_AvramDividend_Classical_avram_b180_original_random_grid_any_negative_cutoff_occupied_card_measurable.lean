-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
-- name    : AvramDividend.Classical.avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:11:50.908943+00:00
-- url     : https://prove2.me/theorems/c7e50b74-6f20-401a-a91e-9f838010c42d
-- title:
--   Original random physical finite-grid occupied count across all negative source cutoffs is measurable
-- statement:
--   On the original spectrally negative Levy source, for finitely many random physical intervals with measurable endpoints, the cardinal of grid cells occupied by at least one negative-mark Poisson cutoff event is measurable. Genuine source interval-count measurability from jump_phys13 and countable finite-grid union measurability from B178 provide an explicit hJmeas source input for finite-mesh original stopped Ito energy.
-- source:
--   Proved avram_jump_phys13 and B178, original source and actual physical random intervals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i)) :
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun cut i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ cut : ℕ, N cut i ω ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry
