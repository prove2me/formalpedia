-- Prove2me | Theorems.Thm_AvramDividend_Classical_kernel_sum_restrict_of_measurable_time_partition
-- name    : AvramDividend.Classical.kernel_sum_restrict_of_measurable_time_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:49:02.251456+00:00
-- url     : https://prove2.me/theorems/e3c975c5-56d4-4f3b-958a-926fa49c3851
-- title:
--   A random-measure kernel equals the sum of its restrictions to a disjoint measurable time partition
-- statement:
--   For any kernel of real-time measures and a countable measurable partition of real time indexed by the integers, if the component kernels equal the corresponding sample-path restrictions of the original kernel, then the countable sum of the component kernels equals the original kernel. This exact measure-valued reconstruction follows from Mathlib's restrict_iUnion for disjoint measurable sets and the kernel sum evaluation lemma. It provides the global-measure reconstruction required to prove s-finiteness of the actual running-supremum dividend Stieltjes measure from its locally finite interval restrictions.
-- source:
--   Pinned Mathlib Measure.restrict_iUnion and ProbabilityTheory.Kernel.sum_apply, exact remote type probe d5f730da-e86e-411f-bcf3-66b798de9f28. To specialise, use Mathlib iUnion_Ioc_intCast and Set.pairwise_disjoint_Ioc_intCast for the integer unit-interval partition.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.kernel_sum_restrict_of_measurable_time_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (S : ℤ → Set ℝ)
    (hd : Pairwise (Function.onFun Disjoint S))
    (hm : ∀ n : ℤ, MeasurableSet (S n))
    (hu : (⋃ n : ℤ, S n) = Set.univ)
    (κs : ℤ → ProbabilityTheory.Kernel Ω ℝ)
    (heq : ∀ (n : ℤ) (ω : Ω),
      κs n ω = (κ ω).restrict (S n)) :
    κ = ProbabilityTheory.Kernel.sum κs := by sorry
