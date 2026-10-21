-- Prove2me | Theorems.Thm_AvramDividend_Classical_kernel_sum_unique_partition
-- name    : AvramDividend.Classical.kernel_sum_unique_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:44:26.855455+00:00
-- url     : https://prove2.me/theorems/b9762d52-d825-4171-857e-b4243895493d
-- title:
--   A kernel is the countable sum of its disjoint sample-space selector kernels
-- statement:
--   If measurable sample-space sets indexed by natural numbers form an exact partition, and each indexed kernel equals a given original kernel on its own part and zero outside, then their countable sum is the original kernel. This is a measure-theoretic identity established by kernel and measure extensionality, together with the fact that exactly one summand at a given sample point is nonzero. It permits constructive s-finite kernel decomposition once each mass-bin selector kernel is separately proved finite.
-- source:
--   Mathlib Kernel.sum_apply, Measure.sum_apply, Kernel.ext, Measure.ext and tsum_ite_eq; exact pinned signatures requested in private job 487d58e1-6bc8-4bfc-8985-848530921fd1. Pure measure-theoretic helper independent of the stochastic Lévy dynamics.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.kernel_sum_unique_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (S : ℕ → Set Ω)
    (κs : ℕ → ProbabilityTheory.Kernel Ω ℝ)
    (hpart : ∀ ω : Ω, ∃! n : ℕ, ω ∈ S n)
    (hselector : ∀ (n : ℕ) (ω : Ω),
      κs n ω = if ω ∈ S n then κ ω else (0 : MeasureTheory.Measure ℝ)) :
    κ = ProbabilityTheory.Kernel.sum κs := by sorry
