-- Prove2me | Theorems.Thm_Champernowne_le_card_blockAt_partial
-- name    : Champernowne.le_card_blockAt_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:01.322154+00:00
-- url     : https://prove2.me/theorems/1100e768-9dda-4477-a339-b510aee4b1ec
-- title:
--   Champernowne: le card block At partial
-- statement:
--   Lower bound for one interior position over a partial cohort.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L273-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L273-L295

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_card_blockAt_partial {b : ℕ} (hb : 1 < b) (K t j : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hj : 0 < j) (hjk : j + w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    t / b ^ w.length ≤ ((Finset.Ico (b ^ K) (b ^ K + t)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card
      + b ^ (K + 1 - j - w.length) := by sorry
