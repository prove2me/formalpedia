-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_exists_uniform_density_bounds
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.exists_uniform_density_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:24.459771+00:00
-- url     : https://prove2.me/theorems/0c08e951-20b1-4f9f-860f-87554f9972e7
-- title:
--   Continuous Positive Density: exists uniform density bounds
-- statement:
--   A strictly positive jointly continuous density on a compact product has a positive uniform lower
--   bound and a finite uniform upper bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L100-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L100-L114

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
open ChannelCapacity.Kernel
open ChannelCapacity.Kernel.ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}
variable [CompactSpace α] [CompactSpace β] [Nonempty α] [Nonempty β]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.exists_uniform_density_bounds
    (h : ContinuousPositiveDensity k ν) :
    ∃ c C : NNReal,
      0 < c ∧ ∀ a b, c ≤ h.density a b ∧ h.density a b ≤ C := by sorry
