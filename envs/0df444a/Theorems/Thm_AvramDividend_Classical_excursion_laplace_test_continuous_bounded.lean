-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_test_continuous_bounded
-- name    : AvramDividend.Classical.excursion_laplace_test_continuous_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:53:46.472977+00:00
-- url     : https://prove2.me/theorems/f0d9f2e8-bd40-4200-acbb-afb18cfa412e
-- title:
--   Bounded continuous Laplace test on the nonnegative half-line
-- statement:
--   For any nonnegative s, the extension to the full real line x↦exp(-s max(x,0)) of the positive-half-line Laplace kernel is continuous, strictly positive and bounded above by one. This provides the bounded continuous test required to pass Laplace transforms through Prokhorov weak limits of finite measures supported on [0,∞), avoiding the unbounded exponential on negative x.
-- source:
--   Direct real-analysis helper for the published Prove2Me excursion_laplace_weak_limit_of_tight_approximants open theorem. Mathlib Analysis.SpecialFunctions.ExpDeriv and FunProp.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

theorem AvramDividend.Classical.excursion_laplace_test_continuous_bounded (s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun x : ℝ => Real.exp (-(s * max x 0))) ∧
      ∀ x : ℝ, 0 < Real.exp (-(s * max x 0)) ∧
        Real.exp (-(s * max x 0)) ≤ 1 := by sorry
