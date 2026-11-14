-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b105_original_random_clock_allnegative_cutoff_occupied_sup_measurable
-- name    : AvramDividend.Classical.avram_b105_original_random_clock_allnegative_cutoff_occupied_sup_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:57:09.304934+00:00
-- url     : https://prove2.me/theorems/0678321b-a72e-4907-a184-89d6f6685f70
-- title:
--   Measurable supremum over all original negative mark cutoffs of genuinely occupied random stopped grid cells
-- statement:
--   For arbitrary finite physical selected grid S with measurable sample-path dependent original source endpoints s_i,t_i, let each negative mark cutoff n count the actual source cells containing at least one genuine original Lévy jump with negative mark at most -1/(n+1). The count per finite cutoff is measurable by the proved original random-interval marked Poisson count theorem. Their countable supremum over all cutoffs is therefore measurable. This creates a measurable all-negative-band occupied-grid count candidate, compatible with arbitrary original infinite negative activity; proving its exact equality with the uncut source occupancy count is the separate future set limit step. No deterministic-clock replacement or global negative second moment.
-- source:
--   Proved avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable and Mathlib ENNReal countable measurable supremum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original negative-band occupied-cell count is measurable for genuine random source grid clocks. -/

theorem AvramDividend.Classical.avram_b105_original_random_clock_allnegative_cutoff_occupied_sup_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ)
    (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i ∈ S, Measurable (s i))
    (ht : ∀ i ∈ S, Measurable (t i)) :
    Measurable (fun ω : Ω =>
      ⨆ cut : ℕ,
        ∑ i ∈ S,
        if ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc (s i ω) (t i ω) ×ˢ
              Iic (-(1 / ((cut : ℝ) + 1)))) ≠ 0 then
          (1 : ℝ≥0∞) else 0) := by sorry
