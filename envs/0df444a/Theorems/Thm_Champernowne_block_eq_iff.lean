-- Prove2me | Theorems.Thm_Champernowne_block_eq_iff
-- name    : Champernowne.block_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:35:23.884808+00:00
-- url     : https://prove2.me/theorems/6c2399b9-8325-4b0d-a0ac-7bc7cc09f7d0
-- title:
--   Champernowne: block eq iff
-- statement:
--   Substring ↔ arithmetic bridge: the block of `w.length` digits at
--   big-endian position `j` of an `m`-digit `n` equals `w` iff the
--   corresponding quotient-remainder is the value of `w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L209-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L209-L246

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.block_eq_iff {b m n : ℕ} (hb : 1 < b)
    (hlen : (bigDigits b n).length = m) {w : List ℕ} (hw : ∀ d ∈ w, d < b)
    {j : ℕ} (hjk : j + w.length ≤ m) :
    ((bigDigits b n).drop j).take w.length = w
      ↔ n / b ^ (m - j - w.length) % b ^ w.length
          = Nat.ofDigits b w.reverse := by sorry
