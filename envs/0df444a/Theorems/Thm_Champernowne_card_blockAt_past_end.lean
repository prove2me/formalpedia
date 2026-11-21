-- Prove2me | Theorems.Thm_Champernowne_card_blockAt_past_end
-- name    : Champernowne.card_blockAt_past_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:35.858402+00:00
-- url     : https://prove2.me/theorems/77bf2fc0-90fb-4661-a06a-82b5a0014ee3
-- title:
--   Champernowne: card block At past end
-- statement:
--   Past the end: no window of length `w.length` starts after `m - w.length`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L457-L469
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L457-L469

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_blockAt_past_end {b : ℕ} (hb : 1 < b) (m j : ℕ) {w : List ℕ}
    (hwne : w ≠ []) (hj : m < j + w.length) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card = 0 := by sorry
