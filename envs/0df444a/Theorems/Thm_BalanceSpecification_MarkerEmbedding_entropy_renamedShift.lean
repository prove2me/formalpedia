-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_entropy_renamedShift
-- name    : BalanceSpecification.MarkerEmbedding.entropy_renamedShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:45:40.564226+00:00
-- url     : https://prove2.me/theorems/f4168b6d-f38b-4d2b-8904-a67b39acb4ec
-- title:
--   Marker Embedding: entropy renamed Shift
-- statement:
--   The manuscript's entropy is unchanged by injective alphabet renaming.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L103-L109
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L103-L109

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]

theorem BalanceSpecification.MarkerEmbedding.entropy_renamedShift [Fintype B] {f : A → B} (hf : Function.Injective f)
    {Y : ShiftSpace A} (hY : Y.carrier.Nonempty) :
    entropy (renamedShift f Y) (renamedShift_nonempty f hY) = entropy Y hY := by sorry
