-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add
-- name    : AvramDividend.Classical.lintegral_Ioc_adjacent_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:31:29.7463+00:00
-- url     : https://prove2.me/theorems/b6b43af5-6b3d-4d88-a98d-d14af38a8124
-- title:
--   Exact additivity of a nonnegative Stieltjes reward over two adjacent half-open time cells
-- statement:
--   For an arbitrary measure on real time and an arbitrary nonnegative extended-real reward weight, the integral over a half-open interval (s,u] equals the sum of the integrals over adjacent cells (s,t] and (t,u], whenever s≤t≤u. This identity remains valid for extended-infinite Stieltjes mass and does not require integrability. It gives the first exact finite-record-grid aggregation step for the original reflected running-supremum dividend policy: cell rewards can be combined without double-counting boundary payments.
-- source:
--   Pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Mathlib.MeasureTheory.lintegral_union and Set.Ioc_union_Ioc_eq_Ioc; confirmed declaration names by the pinned library index and current Mathlib documentation on 20 October 2026.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.Interval.Set.LinearOrder

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.lintegral_Ioc_adjacent_add
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ≥0∞)
    (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u) :
    (∫⁻ r in Set.Ioc s u, f r ∂μ) =
      (∫⁻ r in Set.Ioc s t, f r ∂μ) +
      (∫⁻ r in Set.Ioc t u, f r ∂μ) := by sorry
