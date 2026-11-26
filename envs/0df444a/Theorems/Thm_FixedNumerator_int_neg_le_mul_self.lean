-- Prove2me | Theorems.Thm_FixedNumerator_int_neg_le_mul_self
-- name    : FixedNumerator.int_neg_le_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:19.335056+00:00
-- url     : https://prove2.me/theorems/519b73b4-d216-455d-a924-dde708501c50
-- title:
--   Fixed Numerator: int neg le mul self
-- statement:
--   The Fixed Numerator construction uses the int neg le mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L24-L25
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L24-L25

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.int_neg_le_mul_self (n : ℤ) : -n ≤ n * n ∧ n ≤ n * n := by sorry
