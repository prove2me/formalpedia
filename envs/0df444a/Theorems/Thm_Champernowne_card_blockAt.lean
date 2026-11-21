-- Prove2me | Theorems.Thm_Champernowne_card_blockAt
-- name    : Champernowne.card_blockAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:29.837121+00:00
-- url     : https://prove2.me/theorems/5d15e204-87a3-4131-82e1-e67e20ca5225
-- title:
--   Champernowne: card block At
-- statement:
--   Interior positions: block `w` occurs at position `0 < j` in exactly
--   `(b-1)·b^(m - w.length - 1)` of the `m`-digit numbers, independently of
--   `j` and of `w` itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L359-L396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L359-L396

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_blockAt {b : ℕ} (hb : 1 < b) (m j : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hj : 0 < j) (hjk : j + w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card
      = (b - 1) * b ^ (m - w.length - 1) := by sorry
