-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_negative_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_public_weighted_from_negative_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:08:23.694279+00:00
-- url     : https://prove2.me/theorems/a1baadce-9567-44e7-8f23-8652f933208b
-- title:
--   Public original Lévy predictable weighted marked compensation from strictly negative source rate
-- statement:
--   For the actual original Lévy jump measure, every arbitrary nonnegative weight W measurable in the original past filtration at s, and every Borel jump-mark set B, derive the exact extended-real weighted predictable rectangle mean from the separately established original unconditional ν-rate on B ∩ (-∞,0). No finite intensity or integrability restriction, no independent Poisson replacement, and no use of the target canonical compensator as a hypothesis. This public weighted interface supports P3/P4.
-- source:
--   Pinned public Mathlib and Prove2Me original source: 56a5b5da, c324380a, e13617a2, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_public_weighted_from_negative_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hNegativeRate :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω, W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, W ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
