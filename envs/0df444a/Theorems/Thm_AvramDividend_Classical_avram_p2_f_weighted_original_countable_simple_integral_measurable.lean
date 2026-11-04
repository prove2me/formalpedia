-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_simple_integral_measurable
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_simple_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:52:43.024133+00:00
-- url     : https://prove2.me/theorems/315dcf0b-f988-4716-abec-c790fcb225b3
-- title:
--   Source-original countable marked predictable-simple integral has measurable random total
-- statement:
--   For an actual spectrally negative Lévy source sample and countably many future marked rectangles (s_i,s_i+T_i] × B_i with weights measurable at their respective past times, the literal countable-simple integral against the source intrinsic marked jump measure is measurable on the original sample space. It is derived from the Proved original pathwise marked integral decomposition, the Proved original rectangle-count measurability and the generic countable weighted-mass measurability helper, once that helper is proved. No random-measure kernel postulate and no zero-origin or ν rate.
-- source:
--   Source helper 2bbac71e-ddd6-42a8-afa6-810b47a061f6, d9c55240-a92c-47c2-925f-336ed7cf5d08, pending candidate 24519 for e08df39c-f928-4e07-b6e7-1c076dfef8a6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_simple_integral_measurable
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i)) :
    Measurable (fun ω =>
      (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))) := by sorry
