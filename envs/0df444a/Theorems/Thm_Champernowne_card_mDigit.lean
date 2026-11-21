-- Prove2me | Theorems.Thm_Champernowne_card_mDigit
-- name    : Champernowne.card_mDigit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:49.89224+00:00
-- url     : https://prove2.me/theorems/acd6cf17-6f09-4fa7-9936-90d8108b719a
-- title:
--   Champernowne: card m Digit
-- statement:
--   There are `(b-1) * b^(m-1)` numbers with exactly `m` digits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L139-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L139-L150

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_mDigit {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    (Finset.Ico (b ^ (m - 1)) (b ^ m)).card = (b - 1) * b ^ (m - 1) := by sorry
