-- Prove2me | Theorems.Thm_AvramDividend_Classical_probability_measure_real_Iic_right_continuous
-- name    : AvramDividend.Classical.probability_measure_real_Iic_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:43:35.187017+00:00
-- url     : https://prove2.me/theorems/edb33ccb-efd1-4175-a577-148c0da0f138
-- title:
--   Right continuity of the real CDF of any probability measure on the line
-- statement:
--   For a probability measure μ on the real line, the real-valued distribution function x↦μ((−∞,x]) is right-continuous at every x. The proof connects the actual measure to Mathlib's canonical Stieltjes CDF and its right-continuity axiom.
-- source:
--   Use pinned Mathlib `ProbabilityTheory.cdf_eq_real`, which identifies its StieltjesFunction with μ.real(Iic x), followed by `StieltjesFunction.right_continuous`. This provides the finite-horizon regularity of the Esscher running-infimum CDF, essential for building the infinite-horizon descending law without a global Esscher measure.

import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Stieltjes

open MeasureTheory Set Topology
open ProbabilityTheory

theorem AvramDividend.Classical.probability_measure_real_Iic_right_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => μ.real (Iic y)) (Ici x) x := by sorry
