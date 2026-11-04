-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_event_from_negative_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_public_event_from_negative_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:58:24.102084+00:00
-- url     : https://prove2.me/theorems/0911fd97-37e7-4586-81e3-067b2062d8ef
-- title:
--   Public genuine original Lévy past-event jump compensator bridge from negative Borel intensity
-- statement:
--   For the original spectrally negative Lévy X, its actual left-limit marked jump count on (s,t], and every A measurable in the original F_s, prove the past-event predictable rectangle identity from an independent unconditional ν-rate solely on the strict-negative part of an arbitrary Borel mark set. The source uses only already-Proved public original future extraction and path support; it does not assume the compensator, use a surrogate process, impose finite activity, or require finite ENNReal intensities. This public interface replaces a previously inaccessible private dependency in the P2-E canonical reduction.
-- source:
--   Actual original marked jump measure; pinned Proved public theorems 56a5b5da, c324380a, 5cf3e058 and c5f28e8b, Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_source_rectangle_of_future_extractor_and_unconditional_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_public_event_from_negative_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNegativeRate :
      (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
