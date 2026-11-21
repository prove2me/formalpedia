-- Prove2me | Theorems.Thm_Champernowne_linear_le_const_mul_pow
-- name    : Champernowne.linear_le_const_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:41.936122+00:00
-- url     : https://prove2.me/theorems/89cc5862-6296-4d47-9d9c-f7124d4b1c9e
-- title:
--   Champernowne: linear le const mul pow
-- statement:
--   `c + j + 1 ≤ (c+1) * b^j` for `b ≥ 2` -- linear growth is dominated by
--   any base's exponential, uniformly from `j = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L365-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L365-L373

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.linear_le_const_mul_pow {b : ℕ} (hb : 1 < b) (c j : ℕ) :
    c + j + 1 ≤ (c + 1) * b ^ j := by sorry
