-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_signed_laplace_identification
-- name    : AvramDividend.Classical.contDiffOn_one_of_signed_laplace_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:58:08.027202+00:00
-- url     : https://prove2.me/theorems/35c59184-9cf8-4990-9145-e70fd41c390f
-- title:
--   C1 regularity transfer from signed Laplace identification on the positive half-line
-- statement:
--   Let V be continuous on the positive half-line, and G be a continuously differentiable real-valued function there. If both have integrable, identical Laplace transforms for every rate above a fixed threshold, then V is continuously differentiable too. Apply the Proved signed continuous Laplace-uniqueness theorem, then transfer C1 regularity by pointwise congruence. This is the precise identification bridge needed after constructing a Gaussian Volterra resolvent: no positivity or standing-moment assumptions are introduced.
-- source:
--   Proved continuousOn_Ioi_eq_of_laplace_eq_signed (83290951-5903-4855-9932-c1d5eb47c2e8) and Mathlib ContDiffOn.congr.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.contDiffOn_one_of_signed_laplace_identification
    (V G : ℝ → ℝ) (b : ℝ)
    (hVcont : ContinuousOn V (Ioi (0 : ℝ)))
    (hG : ContDiffOn ℝ 1 G (Ioi (0 : ℝ)))
    (hLap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * V x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * G x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * V x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * G x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
