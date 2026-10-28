-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iic_of_zero_negative
-- name    : AvramDividend.Classical.stieltjes_measure_Iic_of_zero_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:24:43.777135+00:00
-- url     : https://prove2.me/theorems/88214dc2-2b0d-4549-874a-8db9c54f7c6c
-- title:
--   Stieltjes measure of a lower half-line for a CDF zero below the origin
-- statement:
--   A right-continuous nondecreasing real Stieltjes function which vanishes for every negative argument has limit zero at minus infinity. Its Stieltjes measure of the closed lower half-line up to x therefore equals ENNReal.ofReal of the cumulative function at x.
-- source:
--   Show S tends to 0 at minus infinity by eventual equality using the negative-tail hypothesis. Then apply pinned StieltjesFunction.measure_Iic. This is needed to identify the genuine infinite-horizon Esscher descending infimum measure's distribution function.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.Real.Lemmas
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.stieltjes_measure_Iic_of_zero_negative (S : StieltjesFunction ℝ) (hneg : ∀ x : ℝ, x < 0 → S x = 0) (x : ℝ) : S.measure (Iic x) = ENNReal.ofReal (S x) := by sorry
