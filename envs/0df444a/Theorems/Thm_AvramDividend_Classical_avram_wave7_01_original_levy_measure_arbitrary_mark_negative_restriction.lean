-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
-- name    : AvramDividend.Classical.avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:27:57.688545+00:00
-- url     : https://prove2.me/theorems/c324380a-0c39-4f18-8155-c48d6169ceec
-- title:
--   The original Lévy measure of every Borel mark set equals its negative-mark restriction
-- statement:
--   For any original SpectrallyNegativeLevy P 𝓕, whose exact source Lévy triplet has ν([0,∞))=0, the measure of an arbitrary Borel mark set B is exactly its measure of B∩(-∞,0). This source ν identity pairs with the existing Proved pathwise negative support restriction of intrinsic source jump counts, reducing marked intensity identification to negative Borel marks without BV or finite activity.
-- source:
--   Direct measure decomposition into strictly negative and nonnegative parts, disjointness, and the original structure's field X.ν_Ici=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B) :
    X.ν B = X.ν (B ∩ Iio (0 : ℝ)) := by sorry
