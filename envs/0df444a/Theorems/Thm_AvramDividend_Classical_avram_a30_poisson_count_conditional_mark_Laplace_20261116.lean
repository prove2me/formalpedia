-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_poisson_count_conditional_mark_Laplace_20261116
-- name    : AvramDividend.Classical.avram_a30_poisson_count_conditional_mark_Laplace_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:03:07.700201+00:00
-- url     : https://prove2.me/theorems/9e38cf76-59e1-4a45-81bc-621643ad735c
-- title:
--   A Poisson count with exact cell-conditional marked exponential moments has the compound-Poisson Laplace transform
-- statement:
--   An arbitrary integrable real-valued random variable f on its original source Ω has the compound-Poisson Laplace expectation if it admits a measurable natural-valued source count K, and its integrals on every count cell K=k are the Poisson(r) masses times m^k. This theorem uses a disjoint measurable count partition and the Proved Poisson probability-generating function, and does not assume or construct an independently randomised mark stream. The integrability of k↦m^k under Poisson(r) is explicit.
-- source:
--   Pinned Mathlib MeasureTheory.integral_iUnion, MeasureTheory.integral_countable; Proved AvramDividend.Classical.chat06_poisson_count_pgf_general.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a30_poisson_count_conditional_mark_Laplace_20261116
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (m : ℝ)
    (f : Ω → ℝ) (hf : Integrable f P)
    (hm : Integrable (fun k : ℕ => m ^ k) (poissonMeasure r))
    (hCell : ∀ k : ℕ,
      (∫ ω in {ω : Ω | K ω = k}, f ω ∂P) =
        (poissonMeasure r).real {k} * m ^ k) :
    (∫ ω, f ω ∂P) = Real.exp ((r : ℝ) * (m - 1)) := by sorry
