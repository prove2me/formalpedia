-- Prove2me | Theorems.Thm_AvramDividend_Classical_kernel_cutoff_finite_exists
-- name    : AvramDividend.Classical.kernel_cutoff_finite_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:30:38.585915+00:00
-- url     : https://prove2.me/theorems/ad10ab1d-f1d7-478c-afbf-f3c1b35cc928
-- title:
--   A measurable sample-set cut-off of a kernel with a uniform mass bound is a finite kernel
-- statement:
--   Given any measurable kernel on real time, a measurable subset of sample points and a common finite bound on the kernel total mass within that subset, construct a measurable kernel equal to the original kernel on the subset and the zero measure outside. Prove that this selected kernel is uniformly finite with the same bound. This establishes the building block for partitioning a samplewise finite original running-supremum dividend interval measure according to measurable total-mass bins, yielding a countable collection of finite kernels for the exact Mathlib s-finiteness constructor.
-- source:
--   Pinned Mathlib Kernel.mk, Measure.measurable_measure, Kernel.measurable_coe, Measurable.ite and IsFiniteKernel.mk, with exact remote types from private jobs d3e058c6-5f1b-4ebc-ab2c-9d44813a53ee and 37233ed2-97ca-40a4-92e2-ac8eb183605d.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.kernel_cutoff_finite_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (S : Set Ω) (hS : MeasurableSet S)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hBound : ∀ ω : Ω, ω ∈ S → (κ ω) Set.univ ≤ C) :
    ∃ κCut : ProbabilityTheory.Kernel Ω ℝ,
      (∀ ω : Ω, κCut ω =
        if ω ∈ S then κ ω else (0 : MeasureTheory.Measure ℝ)) ∧
      ProbabilityTheory.IsFiniteKernel κCut := by sorry
