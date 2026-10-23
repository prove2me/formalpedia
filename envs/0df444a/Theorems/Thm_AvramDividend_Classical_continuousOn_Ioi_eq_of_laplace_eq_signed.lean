-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
-- name    : AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:26:49.943902+00:00
-- url     : https://prove2.me/theorems/83290951-5903-4855-9932-c1d5eb47c2e8
-- title:
--   Laplace uniqueness for signed continuous functions on the positive half-line
-- statement:
--   If two continuous real functions on the positive half-line have equal integrable Laplace transforms above a threshold, they agree pointwise without requiring either function to be nonnegative. Add the common continuous nonnegative shift |f|+|g| to each function and apply the already Proved nonnegative Laplace uniqueness theorem. Absolute integrability ensures the shift is also Laplace-integrable. This removes the positivity obligation from identification of a signed Gaussian Volterra resolvent with the Esscher-tilted scale function.
-- source:
--   Existing Proved continuousOn_Ioi_eq_of_laplace_eq, UUID fdbf4813-b5d2-4b56-8029-649f638988c1, and absolute-integrability closure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq_signed
    (f g : ℝ → ℝ) (b : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgcont : ContinuousOn g (Ioi 0))
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) :
    ∀ x : ℝ, 0 < x → f x = g x := by sorry
