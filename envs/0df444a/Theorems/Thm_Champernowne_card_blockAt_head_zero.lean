-- Prove2me | Theorems.Thm_Champernowne_card_blockAt_head_zero
-- name    : Champernowne.card_blockAt_head_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:33.764604+00:00
-- url     : https://prove2.me/theorems/c215d400-7d78-4943-83cc-3456eeb87aba
-- title:
--   Champernowne: card block At head zero
-- statement:
--   Head position, leading zero: a block with head `0` never occurs at
--   position `0` of an `m`-digit number.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L473-L516
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L473-L516

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_blockAt_head_zero {b : ℕ} (hb : 1 < b) (m : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hw0 : w.head? = some 0) (hk : w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)).card = 0 := by sorry
