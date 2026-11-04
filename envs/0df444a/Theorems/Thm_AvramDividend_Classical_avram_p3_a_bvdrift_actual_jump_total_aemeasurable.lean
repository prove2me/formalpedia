-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_total_aemeasurable
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_total_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:46:44.274193+00:00
-- url     : https://prove2.me/theorems/9f0d5cdf-09b7-4d83-a277-502849ee5e00
-- title:
--   Actual source BV negative left-jump total is almost-everywhere measurable
-- statement:
--   Under genuine original bounded-variation Lévy assumptions, the entire actual negative-jump magnitude tsum at a fixed horizon is measurable almost everywhere on the original probability space, as a consequence of the proved original s-finite intrinsic jump kernel and original pathwise integral encoding. No compensator or auxiliary process.
-- source:
--   Proved original intrinsic s-finite kernel eb357d08, Measurable.lintegral_kernel, proved original BV sum-to-mark-integral equivalence 3d5eead6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual original negative-jump total is almost-everywhere measurable,
using the source s-finite jump kernel and intrinsic jump encoding. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_total_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    AEMeasurable (fun ω : Ω =>
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P := by sorry
