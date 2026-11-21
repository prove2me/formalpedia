-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_drop_le
-- name    : Champernowne.countOccurrences_drop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:13.169606+00:00
-- url     : https://prove2.me/theorems/9ed0c794-dbe3-41ee-82b5-c2b9fbc16829
-- title:
--   Champernowne: count Occurrences drop le
-- statement:
--   The Champernowne construction uses the count Occurrences drop le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L148-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L148-L151

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_drop_le (w l : List ℕ) (n : ℕ) :
    countOccurrences w (l.drop n) ≤ countOccurrences w l := by sorry
