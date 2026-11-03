-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_outer_measure_negative_mark_support
-- name    : AvramDividend.Classical.avram_wave7_01_original_levy_outer_measure_negative_mark_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:58:23.16488+00:00
-- url     : https://prove2.me/theorems/b8704bc8-8313-4de2-8582-b6e142c83c10
-- title:
--   The source Lévy outer measure ignores nonnegative marks even for arbitrary non-Borel sets
-- statement:
--   For any set B of real marks, not necessarily Borel, the exact original Lévy measure X.ν has the same outer measure on B as on B∩(-∞,0). The proof uses only ν([0,∞))=0 and outer-measure subadditivity/monotonicity, so no Borel or BV assumptions are needed. This strengthens the Proved Borel negative support interface for pathwise localization arguments.
-- source:
--   Original source ν_Ici=0; Mathlib measure_mono and measure_union_le, no separation/finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_levy_outer_measure_negative_mark_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ) :
    X.ν B = X.ν (B ∩ Iio (0 : ℝ)) := by sorry
