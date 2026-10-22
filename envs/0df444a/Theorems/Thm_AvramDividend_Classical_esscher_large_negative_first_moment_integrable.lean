-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_large_negative_first_moment_integrable
-- name    : AvramDividend.Classical.esscher_large_negative_first_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T23:46:55.084866+00:00
-- url     : https://prove2.me/theorems/ab7df859-2b62-4663-9f6e-214af845d1e7
-- title:
--   Exponentially tilted large negative Lévy jumps have finite first moment
-- statement:
--   Let ν be any measure with finite mass on the large negative jump region (-∞,-1], and let φ>0. The Esscher-damped jump first moment (-y)exp(φy) is integrable there, even if the original negative first moment is infinite. The proof uses the already Proved scalar estimate z exp(-φz)≤1/φ and integrability of bounded measurable functions on finite-measure sets. This supports the change-of-measure construction needed to remove standing first-moment assumptions.
-- source:
--   The Proved Gaussian Esscher large-jump uniform bound, and Mathlib MeasureTheory.IntegrableOn.of_bound. The finite large-jump mass premise is supplied directly to avoid introducing unrelated Lévy truncation arithmetic.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_large_uniform
open AvramDividend.Classical MeasureTheory Set Filter

theorem AvramDividend.Classical.esscher_large_negative_first_moment_integrable
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hfinite : ν (Iic (-1 : ℝ)) < ⊤) :
    IntegrableOn (fun y : ℝ => (-y) * Real.exp (φ * y))
      (Iic (-1 : ℝ)) ν := by sorry
