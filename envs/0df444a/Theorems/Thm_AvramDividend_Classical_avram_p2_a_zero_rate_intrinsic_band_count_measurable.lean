-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_intrinsic_band_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:42.836637+00:00
-- url     : https://prove2.me/theorems/a2e7c204-4d22-4f76-aebd-c5554546635d
-- title:
--   Original intrinsic zero-origin Borel-band jump count is measurable
-- statement:
--   For the original source process, every horizon T≥0 and measurable mark set B, the Ω-to-ENNReal intrinsic jump count on (0,T]×B is measurable. It is an exact application of the separately Proved original-source intrinsic σ-finite jump kernel, retaining the same X and probability space. This enables Fatou for the original pathwise count and defines its Borel mean measure, without assuming a compensator or rate identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_intrinsic_band_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B)) := by sorry
