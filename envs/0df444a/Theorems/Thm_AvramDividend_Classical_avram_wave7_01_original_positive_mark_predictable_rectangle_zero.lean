-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_positive_mark_predictable_rectangle_zero
-- name    : AvramDividend.Classical.avram_wave7_01_original_positive_mark_predictable_rectangle_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:03:45.857435+00:00
-- url     : https://prove2.me/theorems/312d9fd3-cfc4-4b3c-a8f2-30ad29b74180
-- title:
--   Original source predictable jump compensation vanishes for strictly positive marks
-- statement:
--   For any original SpectrallyNegativeLevy P 𝓕, every actual source jump mark is non-positive, and ν is supported strictly below zero. Consequently, for any s≤t and any original past event A, the literal source count of strictly positive marks on (s,t] is identically zero and satisfies the prescribed predictable rectangle compensation identity. No BV or finite activity premise is needed.
-- source:
--   Already Proved original jump-mark nonpositivity e95fe5bc-c756-43ca-82d7-acab7078e2eb, original intrinsic jump-count rectangle-to-encard f6336d40-2d19-444f-bacd-83724316de67 and source ν_Ici=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_positive_mark_predictable_rectangle_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Ioi (0 : ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Ioi (0 : ℝ)) := by sorry
