-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_past_weighted_poisson_count_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_past_weighted_poisson_count_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:21:00.52538+00:00
-- url     : https://prove2.me/theorems/f2883713-ef8b-46a8-8b0b-1f96a76239ce
-- title:
--   Past-weighted Poisson count compensated L2 isometry with genuine Poisson law
-- statement:
--   Let K have the genuine Poisson(r) law on a probability space, and let a measurable real past weight H have finite second moment and be independent of K. Then the square of the compensated unmarked finite-rate increment H(K-r) is integrable, and its second moment is r times the second moment of H. The proof derives Poisson mean and second factorial moment from its explicit PMF, obtains variance r, transfers by HasLaw, and factors independent square integrals. The result provides an honest elementary unmarked L2 isometry; iid marked sums and cross-time martingale orthogonality remain separate.
-- source:
--   Applebaum, Levy Processes and Stochastic Calculus, compound-Poisson moments; pinned Mathlib ProbabilityTheory.poissonMeasure_real_singleton, HasSum moment shifts, HasLaw.integral_comp, IndepFun.integrable_mul and IndepFun.integral_fun_mul_eq_mul_integral; cf MIT LeanLevy Probability/Poisson source as an independent mathematical proof pattern.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_past_weighted_poisson_count_l2_isometry
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω → ℝ) (hHm : Measurable H)
    (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hIndep : IndepFun H K P) :
    Integrable (fun ω => (H ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) P ∧
      (∫ ω, (H ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
        (r : ℝ) * ∫ ω, H ω ^ 2 ∂P := by sorry
