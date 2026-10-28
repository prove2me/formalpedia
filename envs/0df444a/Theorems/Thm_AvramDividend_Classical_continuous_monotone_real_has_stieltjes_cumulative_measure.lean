-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_monotone_real_has_stieltjes_cumulative_measure
-- name    : AvramDividend.Classical.continuous_monotone_real_has_stieltjes_cumulative_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:06:21.337878+00:00
-- url     : https://prove2.me/theorems/40aebd85-ab6b-46e4-adc1-5ce1e49cc95a
-- title:
--   Stieltjes measure with exact cumulative law for continuous monotone real functions
-- statement:
--   Every continuous nondecreasing real function whose value tends to zero at minus infinity is the cumulative law of a locally finite Stieltjes measure: the measure of (−∞,x] equals ENNReal.ofReal(F(x)). This wraps Mathlib's Stieltjes function and right-limit construction into a directly reusable real-valued CDF theorem, supporting the unbounded Esscher cumulative Laplace representation milestone.
-- source:
--   Mathlib.MeasureTheory.Measure.Stieltjes; StieltjesFunction.measure_Iic and right limits.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
open MeasureTheory Filter Set
open scoped ENNReal

theorem AvramDividend.Classical.continuous_monotone_real_has_stieltjes_cumulative_measure
    (F : ℝ → ℝ)
    (hMono : Monotone F)
    (hCont : Continuous F)
    (hBot : Tendsto F atBot (nhds 0)) :
    ∃ μ : Measure ℝ, ∀ x : ℝ, μ (Iic x) = ENNReal.ofReal (F x) := by sorry
