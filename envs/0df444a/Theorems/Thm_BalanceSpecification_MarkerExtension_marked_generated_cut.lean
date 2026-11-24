-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_cut
-- name    : BalanceSpecification.MarkerExtension.marked_generated_cut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:59:52.136682+00:00
-- url     : https://prove2.me/theorems/c810193f-f6e9-49e6-af88-3ab7cbf6517f
-- title:
--   Marker Extension: marked generated cut
-- statement:
--   In a finite concatenation of marked generators, every marker is a genuine
--   generator boundary. Cutting there leaves two finite generator concatenations.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L49-L83
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L49-L83

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}

theorem BalanceSpecification.MarkerExtension.marked_generated_cut {P : Set (Word A)} {z p q : Word (Option A)}
    (hz : z ∈ generatedWords (markedCode P)) (heq : z = p ++ none :: q) :
    p ∈ generatedWords (markedCode P) ∧ none :: q ∈ generatedWords (markedCode P) := by sorry
