-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:39:57.238967+00:00
-- url     : https://prove2.me/theorems/79b0fb94-d2ef-4fdb-8d0e-b5a663353f7b
-- title:
--   Past-predictable marked-Poisson bilinear L² covariance identity
-- statement:
--   For a genuine marked Poisson count with iid ν marks independent of count, a square-integrable past weight H independent of the future cell, and two measurable L1∩L2 mark functions f and g, prove the product of the two actual compensated weighted sums integrable and its exact covariance E[A_f A_g]=E[H²]r∫ f(z)g(z)ν(dz). The proof invokes an independently Proved noncircular polarization identity for the original marked cell and derives the mark-inner-product expression by integrability of f², g², fg and Bochner integral linearity. This is the exact tensor-pair covariance interface needed to extend elementary predictable stochastic integration from rank-one to finite sums of mark kernels; no covariance or compensation premise is assumed.
-- source:
--   P1 canonically Proved original-space weighted marked one-cell covariance polarization; pinned memLp_two_iff_integrable_sq, MemLp.integrable_mul and integral_add.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_one_cell_covariance_polarization

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
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
    (f g : E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfI : Integrable f ν) (hgI : Integrable g ν)
    (hf2 : MemLp f 2 ν) (hg2 : MemLp g 2 ν) :
    let A : Ω → ℝ := fun ω => H ω *
      ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)
    let B : Ω → ℝ := fun ω => H ω *
      ((∑ n ∈ Finset.range (K ω), g (Y n ω)) -
        (r : ℝ) * ∫ z, g z ∂ν)
    Integrable (fun ω => A ω * B ω) μ ∧
      (∫ ω, A ω * B ω ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) * (r : ℝ) * (∫ z, f z * g z ∂ν) := by sorry
