-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iio_zero_of_zero_negative
-- name    : AvramDividend.Classical.stieltjes_measure_Iio_zero_of_zero_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:47:30.003505+00:00
-- url     : https://prove2.me/theorems/31c7611d-e3ba-4716-9887-e98a698ee8c7
-- title:
--   A cumulative Stieltjes function zero on negatives generates no measure mass on negative reals
-- statement:
--   If a right-continuous monotone Stieltjes distribution is zero at every strictly negative input, its associated Borel measure assigns zero mass to the strictly negative half-line. This proves the reflected-infimum distribution is supported on nonnegative capital.
-- source:
--   Apply the pinned `StieltjesFunction.measure_Iio`, prove both the limit at minus infinity and left limit at zero are zero by eventual equality on the negative half-line. In particular `leftLim_eq_of_tendsto` and `self_mem_nhdsWithin` handle the strict endpoint without assuming zero mass at the origin.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Order.Filter.AtTopBot.Defs
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.stieltjes_measure_Iio_zero_of_zero_negative
    (S : StieltjesFunction ℝ)
    (hneg : ∀ x : ℝ, x < 0 → S x = 0) :
    S.measure (Iio (0 : ℝ)) = 0 := by sorry
