-- Prove2me | Theorems.Thm_Champernowne_card_blockAt_head
-- name    : Champernowne.card_blockAt_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:33.092119+00:00
-- url     : https://prove2.me/theorems/2bb4b191-70e2-4f89-9b5d-f4915b0dd5a1
-- title:
--   Champernowne: card block At head
-- statement:
--   Head position: a block with nonzero head occurs at position `0` in
--   exactly `b^(m - w.length)` of the `m`-digit numbers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L400-L454
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L400-L454

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_blockAt_head {b : ℕ} (hb : 1 < b) (m : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hw0 : w.head? ≠ some 0)
    (hk : w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)).card
      = b ^ (m - w.length) := by sorry
