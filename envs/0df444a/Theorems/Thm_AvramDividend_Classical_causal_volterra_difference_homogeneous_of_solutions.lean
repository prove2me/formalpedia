-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_difference_homogeneous_of_solutions
-- name    : AvramDividend.Classical.causal_volterra_difference_homogeneous_of_solutions
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:46:52.707453+00:00
-- url     : https://prove2.me/theorems/0074a457-ddc1-4eae-bf5a-9bf009a128dd
-- title:
--   Difference of two Volterra solutions satisfies the homogeneous equation
-- statement:
--   Two continuous locally bounded solutions V and G of the same causal second-kind Volterra equation with leading coefficient a and drift-plus-L1 kernel have a difference D=V−G satisfying aD(x)+∫₀ˣ(β+K(x−s))D(s)ds=0. Establish integrability of each full-kernel product before applying the linearity of the Bochner set integral. This is the algebraic bridge to weighted-contraction uniqueness.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_volterra_difference_homogeneous_of_solutions
    (K V G : ℝ → ℝ) (a β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hGc : ContinuousOn G (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hGb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * V s ∂volume) = x)
    (hGe : ∀ x : ℝ, 0 < x →
      a * G x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * G s ∂volume) = x) :
    ∀ x : ℝ, 0 < x →
      a * (V x - G x) +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * (V s - G s) ∂volume) = 0 := by sorry
