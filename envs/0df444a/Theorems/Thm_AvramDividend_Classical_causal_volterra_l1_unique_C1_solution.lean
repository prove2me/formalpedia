-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_unique_C1_solution
-- name    : AvramDividend.Classical.causal_volterra_l1_unique_C1_solution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:57:41.007919+00:00
-- url     : https://prove2.me/theorems/3839b984-5432-4241-a660-b851b3e242ad
-- title:
--   Global C1 well-posedness and uniqueness for an L1 causal Volterra equation
-- statement:
--   For any strictly positive leading coefficient a, real drift beta and positive-time L1 kernel K, the integrated causal second-kind Volterra equation a G(x)+integral_0^x(beta+K(x-s)) G(s) ds=x has a continuously differentiable, locally bounded solution on x>0. This solution is unique among all positive-time continuous locally bounded solutions. Combine the previously remote-verified existence of a C1 resolvent primitive and the previously remote-verified uniqueness theorem. This assembles the analytic module needed to recognise Lévy Esscher scale functions as canonical Volterra solutions.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_volterra_l1_unique_C1_solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) ∧
      (∀ V : ℝ → ℝ,
        ContinuousOn V (Ioi (0 : ℝ)) →
        (∀ R : ℝ, 0 < R →
          ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C) →
        (∀ x : ℝ, 0 < x →
          a * V x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * V s ∂volume) = x) →
        ∀ x : ℝ, 0 < x → V x = G x) := by sorry
