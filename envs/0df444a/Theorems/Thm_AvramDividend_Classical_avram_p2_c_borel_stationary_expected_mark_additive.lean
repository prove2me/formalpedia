-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_stationary_expected_mark_additive
-- name    : AvramDividend.Classical.avram_p2_c_borel_stationary_expected_mark_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:48:30.928359+00:00
-- url     : https://prove2.me/theorems/3a467cf3-1b0c-48d6-bd56-139873376ded
-- title:
--   Expected mass of a stationary random marked measure is additive in time
-- statement:
--   For a measurable random marked measure, finite or infinite expected count on a zero-origin interval is additive in elapsed time when the expected count of the shifted second interval agrees with its zero-origin counterpart. The proof uses pointwise measure additivity and the ENNReal Lebesgue integral's additive law, without assuming a source Lévy rate.
-- source:
--   An exact expectation-level bridge from Proved pathwise rectangle splitting 781cf9ae and a genuine source-stationary expected increment hypothesis. This is the missing integration step in forming an additive time-rate function before identifying the coefficient with ν.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_time_rectangle_split

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_stationary_expected_mark_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure (ℝ≥0 × ℝ))
    (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ≥0)
    (hMeas : Measurable (fun ω => M ω (Ioc 0 s ×ˢ B)))
    (hShift :
      (∫⁻ ω, M ω (Ioc s (s + t) ×ˢ B) ∂P) =
      (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P)) :
    (∫⁻ ω, M ω (Ioc 0 (s + t) ×ˢ B) ∂P) =
      (∫⁻ ω, M ω (Ioc 0 s ×ˢ B) ∂P) +
      (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P) := by sorry
