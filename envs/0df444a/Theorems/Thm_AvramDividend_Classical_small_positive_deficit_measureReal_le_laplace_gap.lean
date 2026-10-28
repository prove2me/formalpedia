-- Prove2me | Theorems.Thm_AvramDividend_Classical_small_positive_deficit_measureReal_le_laplace_gap
-- name    : AvramDividend.Classical.small_positive_deficit_measureReal_le_laplace_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:08:06.879624+00:00
-- url     : https://prove2.me/theorems/caff41a8-8395-4ed6-9331-905d5ca5e989
-- title:
--   Small positive deficit event probability is bounded by the full Laplace transform minus its zero atom
-- statement:
--   For an integrable small-positive-deficit indicator and nonzero Laplace kernel with measurable zero and small-deficit events, its probability is at most exp(a) times the exact difference between the full Laplace transform and the zero-atom probability. This is the reusable event-probability form of the elementary exponential bound that enters the finite-activity first-jump grid union argument.
-- source:
--   Elementary integral indicator identity in Mathlib and the prior two Proved grid-Laplace helper theorems; Avram, Palmowski and Pistorius (2007) §3.3 equation (3.14).

import Theorems.Thm_AvramDividend_Classical_small_positive_deficit_integral_le_laplace_nonzero
import Theorems.Thm_AvramDividend_Classical_nonzero_laplace_integral_eq_total_sub_zero_atom
import Mathlib.MeasureTheory.Integral.Bochner.Set
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.small_positive_deficit_measureReal_le_laplace_gap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (n a : ℝ)
    (hSmallMeas : MeasurableSet {ω : Ω | 0 < D ω ∧ n * D ω ≤ a})
    (hZeroMeas : MeasurableSet {ω : Ω | D ω = 0})
    (hLeft : Integrable
      (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) μ)
    (hRight : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ)
    (hZero : Integrable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) μ) :
    μ.real {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} ≤
      Real.exp a *
        ((∫ ω, Real.exp (-(n * D ω)) ∂μ) -
          μ.real {ω : Ω | D ω = 0}) := by sorry
