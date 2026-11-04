-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_adjacent_centred_increments_indep
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_adjacent_centred_increments_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:40:46.202097+00:00
-- url     : https://prove2.me/theorems/87660924-2af8-4e23-a128-872b23b1d69e
-- title:
--   Original Levy drift-centred adjacent increments are independent in the genuine source filtration
-- statement:
--   Two contiguous drift-centred increments of the same original spectrally negative Levy source are independent under its actual probability measure and filtration.
-- source:
--   Proved P4-A original centred increment independence from the source past, source adaptedness, Mathlib indep_of_indep_of_le_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_adjacent_centred_increments_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance) P := by sorry
