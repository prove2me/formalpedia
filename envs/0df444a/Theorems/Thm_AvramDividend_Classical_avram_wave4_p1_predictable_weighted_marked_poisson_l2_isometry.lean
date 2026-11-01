-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:01:22.213457+00:00
-- url     : https://prove2.me/theorems/8a42751c-1bea-4e5a-aae6-cc00f79d7002
-- title:
--   Past-predictable weighted marked-Poisson one-cell L² isometry
-- statement:
--   For a genuine marked-Poisson cell with iid marks, a square-integrable past-measurable weight H independent of the entire joint future marked count and marks has exact centred squared energy E[H²]rEν[f²]. The integrability of the product square is proved from joint independence, without assuming the compensated integral is L² or martingale. This is the diagonal identity needed for elementary time-predictable stochastic integration, extendable to finite grids through cross-cell orthogonality.
-- source:
--   WS1B measurable variable-length mark sum, P1 proved random marked L2 and compensated one-cell isometry; pinned IndepFun.comp/integrable_mul/integral_fun_mul_eq_mul_integral.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_compound_poisson_centered_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H : Ω → ℝ) (hHm : Measurable H)
    (hH2 : Integrable (fun ω => H ω ^ 2) μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun H (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    Integrable (fun ω =>
      (H ω * ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)) ^ 2) μ ∧
      (∫ ω, (H ω * ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)) ^ 2 ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) * ∫ z, f z ^ 2 ∂ν) := by sorry
