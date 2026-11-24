-- Prove2me | Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
-- name    : BalanceSpecification.follower_card_reverseLanguage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:19.880804+00:00
-- url     : https://prove2.me/theorems/a9320195-4c4a-4cbc-ab31-f2f0bfa78205
-- title:
--   Balance Specification: follower card reverse Language
-- statement:
--   The Balance Specification construction uses the follower card reverse Language property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L156-L176
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L156-L176

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.follower_card_reverseLanguage (L : Set (Word A)) (u : Word A) (n : ℕ) :
    (followerFinset (reverseLanguage L) u n).card =
      (predecessorFinset L u.reverse n).card := by sorry
