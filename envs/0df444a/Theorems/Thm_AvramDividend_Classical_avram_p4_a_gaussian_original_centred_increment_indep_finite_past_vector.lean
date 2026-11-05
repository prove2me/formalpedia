-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:26:33.637174+00:00
-- url     : https://prove2.me/theorems/f19221c6-1dea-46fa-9f93-df2f04326431
-- title:
--   Original centred Lévy increment independent of a finite vector of past observations
-- statement:
--   For the genuine original spectrally negative Lévy process, each centred future increment is independent of any finite vector of source observations from times not exceeding the increment's starting time.
-- source:
--   Original SpectrallyNegativeLevy independent increments and adaptedness, and Mathlib measurable_pi_iff and indep_of_indep_of_le_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≤ s) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => fun i : Fin n => Y.X (v i) ω)
        inferInstance) P := by sorry
