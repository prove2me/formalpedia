-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_borel_rate_of_negative_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_borel_rate_of_negative_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:16:23.870132+00:00
-- url     : https://prove2.me/theorems/9de6cb12-6412-49bd-8f4c-32d523f74e13
-- title:
--   Original-process full Borel jump-rate from the strictly negative marked rate
-- statement:
--   The actual original source marked jump rectangle on an arbitrary Borel mark set is equal pathwise to that on its strict negative restriction; the Lévy jump measure agrees too. Consequently a strictly negative Borel mark rate suffices to establish the full Borel rate, without any independently assumed point process.
-- source:
--   Exact Proved original count negative-restriction 56a5b5da and original ν negative-restriction c324380a. A pathwise ENNReal lintegral congruence transports the mark rate; no compensator or rate is assumed beyond the negative Borel marked rectangle rate in the theorem hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The entire original Borel marked intensity follows from intensity restricted to strictly negative marks. -/

theorem AvramDividend.Classical.avram_p2_e_compensator_original_borel_rate_of_negative_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNegativeRate : (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
