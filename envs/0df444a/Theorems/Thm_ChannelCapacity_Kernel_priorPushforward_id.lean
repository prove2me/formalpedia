-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
-- name    : ChannelCapacity.Kernel.priorPushforward_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:00.831296+00:00
-- url     : https://prove2.me/theorems/abac8d7a-7d92-4a2e-816b-72b1c3bae564
-- title:
--   Kernel: prior Pushforward id
-- statement:
--   The Kernel construction uses the prior Pushforward id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L103-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L103-L107

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

theorem ChannelCapacity.Kernel.priorPushforward_id (p : ProbabilityMeasure α) :
    Kernel.priorPushforward (Kernel.id : Kernel α α) p = p := by sorry
