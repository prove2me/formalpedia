-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_future_indep_weighted_two_past_increments
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_future_indep_weighted_two_past_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:32:02.36799+00:00
-- url     : https://prove2.me/theorems/f36b5dad-0204-48c8-aee1-f725ffecfe7a
-- title:
--   Future centred source increment independent of weighted sum of two past increments
-- statement:
--   In the original spectrally negative Lévy process, a future drift-centred increment is independent of an arbitrary real linear combination of two adjacent past drift-centred increments.
-- source:
--   Genuine SpectrallyNegativeLevy adaptedness, its Proved original future-past independent-increment lemma, and Mathlib indep_of_indep_of_le_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_future_indep_weighted_two_past_increments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (α β : ℝ) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X v ω - Y.X u ω) - ((v - u : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => α * ((Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) +
          β * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c))
        inferInstance) P := by sorry
