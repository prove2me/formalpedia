-- Prove2me | Theorems.Thm_BalanceSpecification_interiorLanguage_antitone
-- name    : BalanceSpecification.interiorLanguage_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:02.058626+00:00
-- url     : https://prove2.me/theorems/bed53502-8f5b-42d8-adcc-f1c4add74703
-- title:
--   Balance Specification: interior Language antitone
-- statement:
--   The Balance Specification construction uses the interior Language antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L33-L36
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L33-L36

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.interiorLanguage_antitone {L : Set (Word A)} {M N : ℕ} (hMN : M ≤ N) :
    interiorLanguage L N ⊆ interiorLanguage L M := by sorry
