-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_infix
-- name    : BalanceSpecification.MarkerExtension.marked_generated_infix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:18.943452+00:00
-- url     : https://prove2.me/theorems/1418e87d-dc59-40f4-86b6-1b97b659fdee
-- title:
--   Marker Extension: marked generated infix
-- statement:
--   Every marker-free subword of a finite marked concatenation lies within one
--   actual payload; no boundary can be crossed without including a marker.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L121-L157
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L121-L157

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

theorem BalanceSpecification.MarkerExtension.marked_generated_infix {P : Set (Word A)} (hP : P.Nonempty)
    {z w : Word (Option A)} (hz : z ∈ generatedWords (markedCode P))
    (hw : none ∉ w) (hinfix : w <:+: z) : ∃ v ∈ P, w <:+: v.map some := by sorry
