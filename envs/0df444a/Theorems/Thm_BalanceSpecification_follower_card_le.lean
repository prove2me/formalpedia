-- Prove2me | Theorems.Thm_BalanceSpecification_follower_card_le
-- name    : BalanceSpecification.follower_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:40.156259+00:00
-- url     : https://prove2.me/theorems/4bc21c79-015a-44e5-9ac8-8bb47b56ef21
-- title:
--   Balance Specification: follower card le
-- statement:
--   The Balance Specification construction uses the follower card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L79-L82
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L79-L82

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]

theorem BalanceSpecification.follower_card_le (L : Set (Word A)) (u : Word A) (n : ℕ) :
    (followerFinset L u n).card ≤ wordCount L n := by sorry
