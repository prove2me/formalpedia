-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_le_take_add_drop
-- name    : Champernowne.countOccurrences_le_take_add_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:12.894539+00:00
-- url     : https://prove2.me/theorems/62142959-cdae-4097-916c-aa458ce178b1
-- title:
--   Champernowne: count Occurrences le take add drop
-- statement:
--   Cutting at `n` loses at most `w.length` (seam) occurrences.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L154-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L154-L159

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_le_take_add_drop (w l : List ℕ) (n : ℕ) :
    countOccurrences w l
      ≤ countOccurrences w (l.take n) + countOccurrences w (l.drop n)
        + w.length := by sorry
