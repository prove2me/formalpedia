-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_le_boundary_mul_interior
-- name    : BalanceSpecification.wordCount_le_boundary_mul_interior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:34.889008+00:00
-- url     : https://prove2.me/theorems/8b6a3595-7834-415d-8e0c-3487b47120ed
-- title:
--   Balance Specification: word Count le boundary mul interior
-- statement:
--   Splitting off two boundary words controls the number of long words by their interiors.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L59-L113
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L59-L113

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

theorem BalanceSpecification.wordCount_le_boundary_mul_interior (L : Set (Word A)) (M t : ℕ) :
    wordCount L (2 * M + t) ≤ (Fintype.card A) ^ (2 * M) *
      wordCount (interiorLanguage L M) t := by sorry
