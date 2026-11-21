-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_convexCombination
-- name    : ChannelCapacity.Kernel.priorPushforward_convexCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:58.080819+00:00
-- url     : https://prove2.me/theorems/df3e697c-1871-442d-91d1-3fdd751711ac
-- title:
--   Kernel: prior Pushforward convex Combination
-- statement:
--   The Kernel construction uses the prior Pushforward convex Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L81-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L81-L100

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
open ChannelCapacity.Kernel

theorem ChannelCapacity.Kernel.priorPushforward_convexCombination (k : Kernel α β) [IsMarkovKernel k]
    (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    Kernel.priorPushforward k (ProbabilityMeasure.convexCombination p q t ht) =
      ProbabilityMeasure.convexCombination
        (Kernel.priorPushforward k p)
        (Kernel.priorPushforward k q)
        t ht := by sorry
