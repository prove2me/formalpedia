-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
-- name    : ChannelCapacity.Kernel.priorPushforward_dirac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:59.423741+00:00
-- url     : https://prove2.me/theorems/64899cca-b85c-496f-bae7-85acdb02a98e
-- title:
--   Kernel: prior Pushforward dirac
-- statement:
--   The Kernel construction uses the prior Pushforward dirac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L71-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L71-L79

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

theorem ChannelCapacity.Kernel.priorPushforward_dirac (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    Kernel.priorPushforward k (MeasureTheory.diracProba a) =
      (⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩ :
        ProbabilityMeasure β) := by sorry
