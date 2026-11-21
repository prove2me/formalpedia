-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_klDiv_le_outputPrior_bound
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.row_klDiv_le_outputPrior_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:22.071694+00:00
-- url     : https://prove2.me/theorems/02974cd4-d0ca-4158-9340-6f4ff4df3410
-- title:
--   Continuous Positive Density: row kl Div le output Prior bound
-- statement:
--   The Continuous Positive Density construction uses the row kl Div le output Prior bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L221-L336
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L221-L336

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
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
omit [BorelSpace α] [BorelSpace β]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.row_klDiv_le_outputPrior_bound
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ a : α, InformationTheory.klDiv (k a) (outputPrior k p).toMeasure ≤ B := by sorry
