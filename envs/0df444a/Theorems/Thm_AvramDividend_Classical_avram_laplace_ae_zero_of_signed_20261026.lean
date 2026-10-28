-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_laplace_ae_zero_of_signed_20261026
-- name    : AvramDividend.Classical.avram_laplace_ae_zero_of_signed_20261026
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:09:58.487338+00:00
-- url     : https://prove2.me/theorems/a9ef580a-41ca-49d0-93a4-f5d4d88bceea
-- title:
--   Signed Laplace-transform uniqueness without continuity
-- statement:
--   A signed residual with integrable exponential weights and zero Laplace integral at every parameter above b vanishes almost everywhere on the positive half-line. Splitting into R+|R| and |R| reduces the assertion to the established nonnegative Laplace uniqueness theorem. This removes the continuity and C2 assumptions of previous generator-residual identification results and can serve bounded- and unbounded-variation analytic branches.
-- source:
--   Proved AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_c_two_residual_vanishing, candidate 16533, and Proved avram_laplace_ae_eq_of_nonnegative_20261026, candidate 16513.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_avram_laplace_ae_eq_of_nonnegative_20261026
open AvramDividend.Classical MeasureTheory Set

/-- A signed function with zero Laplace transform on a real half-line
vanishes almost everywhere on positive arguments. -/
theorem AvramDividend.Classical.avram_laplace_ae_zero_of_signed_20261026
    (R : ℝ → ℝ) (b : ℝ)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * R x) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) = 0) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), R x = 0 := by sorry
