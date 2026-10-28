-- Prove2me | Theorems.Thm_AvramDividend_Classical_small_positive_deficit_integral_le_laplace_nonzero
-- name    : AvramDividend.Classical.small_positive_deficit_integral_le_laplace_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:51:37.13571+00:00
-- url     : https://prove2.me/theorems/6f3166fa-69f1-4ce4-8031-5856d6819a8f
-- title:
--   Small positive drift-deficit probability controlled by the nonzero Laplace contribution
-- statement:
--   For any integrable nonnegative indicator of a small positive deficit and integrable nonzero Laplace contribution, the indicator expectation is at most exp(a) times the nonzero Laplace expectation whenever 0<D and nD≤a. This direct exponential indicator inequality underpins the finite-grid proof that the first strictly positive bounded-variation Lévy drift deficit forces the true zero-barrier drawdown clock to stop.
-- source:
--   Elementary exponential monotonicity; proof programme for Avram, Palmowski and Pistorius (2007), §3.3 equation (3.14), https://arxiv.org/pdf/math/0702893.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
open MeasureTheory Set

theorem AvramDividend.Classical.small_positive_deficit_integral_le_laplace_nonzero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (n a : ℝ)
    (hLeft : Integrable
      (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) μ)
    (hRight : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ) :
    (∫ ω, if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0 ∂μ) ≤
      Real.exp a *
        (∫ ω, if D ω = 0 then (0 : ℝ)
          else Real.exp (-(n * D ω)) ∂μ) := by sorry
