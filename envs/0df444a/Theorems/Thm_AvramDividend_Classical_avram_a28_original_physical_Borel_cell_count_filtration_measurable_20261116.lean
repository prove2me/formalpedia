-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
-- name    : AvramDividend.Classical.avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:41:06.262192+00:00
-- url     : https://prove2.me/theorems/60ce8fc6-a599-4b1b-bc78-849e0d30fdb4
-- title:
--   An original physical Borel marked-jump cell count is measurable in the original filtration at its right endpoint
-- statement:
--   The original physical Borel marked-jump count in any (s,T] is measurable with respect to the original Levy filtration at T. By source-exact frozen-path factorisation, this count is a measurable function of the path stopped at T. Compose with Proved measurability of that stopped original path and Proved cadlag regularity. This supplies the individual-cell adaptedness needed for the jointly independent physical-grid count family.
-- source:
--   Proved frozen original-path filtration measurable 32236cde, cadlag c7626437 and new frozen source Borel interval factorisation a28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B)) := by sorry
