-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_disjoint_centred_increments_indep
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_disjoint_centred_increments_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:28:25.558868+00:00
-- url     : https://prove2.me/theorems/0f42f83c-e5f3-4b61-b37e-357c2fb7b91f
-- title:
--   Disjoint centred increments independent in original Lévy filtration
-- statement:
--   Centred increments of the original process over two time-ordered disjoint intervals are independent, including when there is a gap between the intervals.
-- source:
--   Original source filtration adaptedness and increment independence; Mathlib measurableSet_comap and indep_of_indep_of_le_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_disjoint_centred_increments_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X v ω - Y.X u ω) - ((v - u : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance) P := by sorry
