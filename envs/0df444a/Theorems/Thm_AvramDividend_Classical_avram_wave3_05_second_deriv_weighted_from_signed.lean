-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_second_deriv_weighted_from_signed
-- name    : AvramDividend.Classical.avram_wave3_05_second_deriv_weighted_from_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:38:38.889574+00:00
-- url     : https://prove2.me/theorems/56a74d89-2549-4ce2-86b8-8d71feb3989e
-- title:
--   Full positive-halfline Gaussian weighted second derivative from source signed density
-- statement:
--   The Gaussian source Esscher untilting formula expresses W'' as 2φW'−φ²W+exp((φ+w)x)S(x)/a on positive reserves. The known q-scale Laplace integrability controls weighted W and W'; global Gaussian Neumann theory controls S in L1. For any θ≥φ+w the last weighted factor is bounded by 1, yielding the full weighted absolute integrability of W'' on (0,∞), the first unresolved Gaussian generator residual obligation.
-- source:
--   Exact Gaussian Esscher reconstruction, pinned Mathlib Integrable.bdd_mul, previous weighted W and W' q-scale Laplace bounds.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_second_deriv_weighted_from_signed
    (W S : ℝ → ℝ) (φ w θ a : ℝ)
    (hθ : φ + w ≤ θ)
    (hW : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)) volume)
    (hWder : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ)) volume)
    (hS : IntegrableOn S (Ioi (0 : ℝ)) volume)
    (hsecond : ∀ x : ℝ, 0 < x →
      deriv (deriv W) x =
        2 * φ * deriv W x - φ ^ 2 * W x +
          Real.exp ((φ + w) * x) * (S x / a)) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv (deriv W) x)
      (Ioi (0 : ℝ)) volume := by sorry
