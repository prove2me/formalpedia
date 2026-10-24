-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_survival_probability_monotone
-- name    : AvramDividend.Classical.esscher_survival_probability_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:42:46.594979+00:00
-- url     : https://prove2.me/theorems/9fbe2d43-0568-4dec-b043-2d1baa9f8f3a
-- title:
--   All-time survival probability is monotone in initial reserve
-- statement:
--   For any measurable path space, measure P, and real-valued path process Z, the measure of paths staying above negative x forever is no larger than the measure of paths staying above negative y forever when x≤y. This pathwise fact supplies the monotonicity of the all-time survival distribution in the independent non-circular Esscher change-of-measure construction of the tilted scale function.
-- source:
--   Elementary event inclusion and monotonicity of outer measure, preparatory to the positive-mean survival representation of zero-scale functions in Kuznetsov, Kyprianou and Rivero (2012), Theorem 2.1.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.esscher_survival_probability_monotone
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (x y : ℝ) (hxy : x ≤ y) :
    P {ω | ∀ t : ℝ≥0, 0 ≤ x + Z t ω} ≤
      P {ω | ∀ t : ℝ≥0, 0 ≤ y + Z t ω} := by sorry
