-- Prove2me | Theorems.Thm_Champernowne_length_bigDigits_eq
-- name    : Champernowne.length_bigDigits_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:35:17.113785+00:00
-- url     : https://prove2.me/theorems/ae60f5b8-b175-4323-af5c-aeeebc556cce
-- title:
--   Champernowne: length big Digits eq
-- statement:
--   A number in `[b^(m-1), b^m)` has exactly `m` digits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L126-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L126-L134

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.length_bigDigits_eq {b m n : ℕ} (hb : 1 < b)
    (h1 : b ^ (m - 1) ≤ n) (h2 : n < b ^ m) :
    (bigDigits b n).length = m := by sorry
