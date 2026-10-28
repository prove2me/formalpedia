-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonzero_laplace_integral_eq_total_sub_zero_atom
-- name    : AvramDividend.Classical.nonzero_laplace_integral_eq_total_sub_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:00:17.202058+00:00
-- url     : https://prove2.me/theorems/d436b2d0-b898-42be-92e0-ff6da8297ed9
-- title:
--   Remove the zero atom from a real Laplace transform
-- statement:
--   The Laplace transform contribution from strictly nonzero residual values equals the full transform minus the probability mass at zero. The proof is a pointwise split exp(-nD)=1_{D=0}+1_{D≠0}exp(-nD) integrated using the supplied integrability of both terms. It pairs with the small positive deficit indicator bound and the actual Lévy exponential transform/atom formulas in the finite-activity zero-barrier grid argument.
-- source:
--   Elementary measurable integration and the actual Lévy Laplace-atom decomposition needed for Avram, Palmowski and Pistorius (2007), §3.3 equation (3.14).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
open MeasureTheory Set

theorem AvramDividend.Classical.nonzero_laplace_integral_eq_total_sub_zero_atom
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (n : ℝ)
    (hNonzero : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ)
    (hZero : Integrable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) μ) :
    (∫ ω, if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω)) ∂μ) =
      (∫ ω, Real.exp (-(n * D ω)) ∂μ) -
        (∫ ω, if D ω = 0 then (1 : ℝ) else 0 ∂μ) := by sorry
