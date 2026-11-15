-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b187_original_all_negative_cutoff_occupied_random_grid_count_measurable
-- name    : AvramDividend.Classical.avram_b187_original_all_negative_cutoff_occupied_random_grid_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:44:27.249947+00:00
-- url     : https://prove2.me/theorems/57740435-3b86-4ef8-bacc-fea894b728b8
-- title:
--   True original random-grid occupied negative Poisson source cell count across all reciprocal cutoffs is measurable
-- statement:
--   For the genuine original spectrally negative Lévy process and an arbitrary finite family of original physical clock intervals whose left and right endpoints are measurable random maps, mark exactly the cells where at least one negative reciprocal cutoff band has a nonzero original mapped negative Poisson count. The real cardinal of this countably occupied source grid Finset is measurable. Proved original jump_phys13 establishes measurable original random-clock negative-band Poisson count for each fixed cutoff and cell. The nonzero event is measurable, and prepared B178 provides the finite-grid cardinal measurability under a countable union of such events. This is a direct original-source intermediate for B180, which equates the countably occupied original marked cells to the genuine physical nonzero source jump-containing cell Finset via B179 and B118. Publish when B178 is authoritatively Proved.
-- source:
--   Proved original jump_phys13 random marked Poisson band count measurable, prepared B178 generic countable finite occupied-grid cardinal measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b178_generic_countable_cutoff_occupied_finite_grid_card_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The number of original random physical grid cells occupied by at least one reciprocal negative-cutoff marked Poisson source is a measurable real random variable. -/

theorem AvramDividend.Classical.avram_b187_original_all_negative_cutoff_occupied_random_grid_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i)) :
    let N : Ω → ℕ → ℕ → ℝ≥0∞ := fun ω n i =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ n : ℕ, N ω n i ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry
