-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_id_injectivePriorPushforward
-- name    : ChannelCapacity.Kernel.id_injectivePriorPushforward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:02.822286+00:00
-- url     : https://prove2.me/theorems/3f385442-7102-4a7f-8677-49400a75413d
-- title:
--   Kernel: id injective Prior Pushforward
-- statement:
--   The Kernel construction uses the id injective Prior Pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L109-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L109-L112

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

theorem ChannelCapacity.Kernel.id_injectivePriorPushforward :
    Kernel.InjectivePriorPushforward (Kernel.id : Kernel α α) := by sorry
