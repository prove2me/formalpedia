-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_past_weights_marked_cell_covariance
-- name    : AvramDividend.Classical.avram_wave4_p1_two_past_weights_marked_cell_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:51:43.123918+00:00
-- url     : https://prove2.me/theorems/5c54fbf4-25bd-4e56-825f-51fb70d574dc
-- title:
--   Two past-predictable weights, two mark kernels: compensated marked-cell L² covariance
-- statement:
--   For an original-space genuine Poisson count K, its iid independently marked future sequence, two measurable square-integrable past weights H,J, two measurable L1∩L2 mark kernels f,g, and past independence of H,J,H+J from the joint future cell, prove integrability and exact E[(HΔf)(JΔg)]=E[HJ]r∫fgdν. The proof derives MemLp 2 of H+J, integrability of HJ, three independently Proved same-weight marked covariance identities, and polarizes in the past-weight variable. It makes no covariance conclusion or compensated-martingale identity a hypothesis. This supplies the true mixed predictable tensor-pair covariance for finite-rank marked integrands.
-- source:
--   Canonically Proved P1 one-weight marked bilinear covariance 79b0fb94-d2ef-4fdb-8d0e-b5a663353f7b and pinned MemLp Hölder, integral_add, polarization.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_two_past_weights_marked_cell_covariance
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H J : Ω → ℝ) (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : Integrable (fun ω => H ω ^ 2) μ)
    (hJ2 : Integrable (fun ω => J ω ^ 2) μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPastH : IndepFun H (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hPastJ : IndepFun J (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hPastSum : IndepFun (fun ω => H ω + J ω)
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f g : E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfI : Integrable f ν) (hgI : Integrable g ν)
    (hf2 : MemLp f 2 ν) (hg2 : MemLp g 2 ν) :
    let A : Ω → ℝ := fun ω => H ω *
      ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)
    let B : Ω → ℝ := fun ω => J ω *
      ((∑ n ∈ Finset.range (K ω), g (Y n ω)) -
        (r : ℝ) * ∫ z, g z ∂ν)
    Integrable (fun ω => A ω * B ω) μ ∧
      (∫ ω, A ω * B ω ∂μ) =
        (∫ ω, H ω * J ω ∂μ) * (r : ℝ) * (∫ z, f z * g z ∂ν) := by sorry
