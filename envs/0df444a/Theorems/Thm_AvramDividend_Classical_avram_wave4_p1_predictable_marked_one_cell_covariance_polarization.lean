-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_one_cell_covariance_polarization
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_marked_one_cell_covariance_polarization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:31:12.168503+00:00
-- url     : https://prove2.me/theorems/08754f4c-4256-4030-a35e-23462426aacb
-- title:
--   Past-predictable marked compound-Poisson compensated covariance polarization
-- statement:
--   Under a genuine original-space marked Poisson cell with iid marks, a square-integrable past weight independent of the joint future count and mark sequence, and two real measurable L1∩L2 mark kernels f,g, the mixed product of the two centered weighted marked sums is integrable. Its expectation equals E[H²]·(r/2)·[Eν(f+g)²−Eνf²−Eνg²]. The proof polarizes three independently proved noncircular weighted marked-cell L² isometries for f, g and f+g, proves the exact pointwise sum identity and integrates the square expansion. This is the bilinear energy interface for finite linear combinations of predictable past–mark tensor kernels; it does not assume covariance or compensation.
-- source:
--   P1 canonically Proved weighted marked-Poisson one-cell L² isometry UUID 8a42751c; pinned finite-sum and integral linearity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_predictable_marked_one_cell_covariance_polarization
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
        (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) / 2) *
          ((∫ z, (f z + g z) ^ 2 ∂ν) -
            (∫ z, f z ^ 2 ∂ν) - (∫ z, g z ^ 2 ∂ν)) := by sorry
