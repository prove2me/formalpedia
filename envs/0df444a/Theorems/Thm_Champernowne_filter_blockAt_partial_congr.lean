-- Prove2me | Theorems.Thm_Champernowne_filter_blockAt_partial_congr
-- name    : Champernowne.filter_blockAt_partial_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:57.061662+00:00
-- url     : https://prove2.me/theorems/d98f6981-e920-429c-b071-c6f7a0ee50fd
-- title:
--   Champernowne: filter block At partial congr
-- statement:
--   Convert the block predicate at position `j` to the arithmetic
--   predicate, on a partial cohort of `(K+1)`-digit numbers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L258-L270
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L258-L270

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.filter_blockAt_partial_congr {b : ℕ} (hb : 1 < b) (K t j : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hjk : j + w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)
      = (Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => n / b ^ (K + 1 - j - w.length) % b ^ w.length
        = Nat.ofDigits b w.reverse) := by sorry
