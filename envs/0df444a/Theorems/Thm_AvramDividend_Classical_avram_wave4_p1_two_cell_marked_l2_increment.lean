-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_cell_marked_l2_increment
-- name    : AvramDividend.Classical.avram_wave4_p1_two_cell_marked_l2_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:12:39.801636+00:00
-- url     : https://prove2.me/theorems/f9488540-ce76-4a30-9c53-8b8d599aa0c8
-- title:
--   Original-space marked predictable two-cell L² energy increment
-- statement:
--   With a square-integrable preceding payoff H and a square-integrable next-cell predictable weight J, both jointly independent of the future fully iid marked Poisson cell, the squared integral of H+J(S_K-rEνf) is integrable and has expectation E H² + E J²*r Eνf². Uses genuine marked future cross orthogonality for the mixed term and weighted marked isometry for the diagonal. The weights may be dependent; no martingale conclusion appears in hypotheses. This is the inductive step for a finite-grid stopped marked-Poisson L² isometry.
-- source:
--   P1 full marked weighted one-cell isometry and P1 marked future cross orthogonality, only after both become canonically Proved; pinned integral_add and quadratic expansion.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_future_cross_orthogonality

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_two_cell_marked_l2_increment
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H J : Ω → ℝ) (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : MemLp H 2 μ) (hHSq : Integrable (fun ω => H ω ^ 2) μ)
    (hJ2 : MemLp J 2 μ) (hJSq : Integrable (fun ω => J ω ^ 2) μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun (fun ω => (H ω, J ω))
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    Integrable (fun ω => (H ω + J ω *
        ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
          (r : ℝ) * ∫ z, f z ∂ν)) ^ 2) μ ∧
      (∫ ω, (H ω + J ω *
        ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
          (r : ℝ) * ∫ z, f z ∂ν)) ^ 2 ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) +
          (∫ ω, J ω ^ 2 ∂μ) * ((r : ℝ) * ∫ z, f z ^ 2 ∂ν) := by sorry
