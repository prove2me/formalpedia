-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_tiling_le
-- name    : BalanceSpecification.wordCount_tiling_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:54.351443+00:00
-- url     : https://prove2.me/theorems/3405f945-91da-4413-ae83-7ca7b80fb478
-- title:
--   Balance Specification: word Count tiling le
-- statement:
--   Long words are encoded by their two boundary pieces and their interior tiles.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L128-L144
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L128-L144

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
variable [Fintype A]

theorem BalanceSpecification.wordCount_tiling_le {L K : Set (Word A)} (hL : IsFactorial L) (M n k : ℕ)
    (hcore : ∀ w ∈ interiorLanguage L M, w.length = n → w ∈ K) :
    wordCount L (2 * M + k * n) ≤
      (Fintype.card A) ^ (2 * M) * (wordCount K n) ^ k := by sorry
