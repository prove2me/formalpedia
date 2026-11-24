-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_suffix
-- name    : BalanceSpecification.MarkerExtension.marked_generated_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:19.632077+00:00
-- url     : https://prove2.me/theorems/9e4d9d38-3de4-4034-8585-6c8cac3343dd
-- title:
--   Marker Extension: marked generated suffix
-- statement:
--   A marker-free suffix of a finite marked concatenation is a suffix of one
--   actual payload. The empty suffix is included.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L93-L117
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L93-L117

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

theorem BalanceSpecification.MarkerExtension.marked_generated_suffix {P : Set (Word A)} (hP : P.Nonempty)
    {z w : Word (Option A)} (hz : z ∈ generatedWords (markedCode P))
    (hw : none ∉ w) (hsuffix : w <:+ z) : ∃ v ∈ P, w <:+ v.map some := by sorry
