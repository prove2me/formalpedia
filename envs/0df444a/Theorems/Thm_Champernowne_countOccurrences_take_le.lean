-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_take_le
-- name    : Champernowne.countOccurrences_take_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:09.910144+00:00
-- url     : https://prove2.me/theorems/832b0d73-e9c3-4eb2-b79c-650ecc862154
-- title:
--   Champernowne: count Occurrences take le
-- statement:
--   The Champernowne construction uses the count Occurrences take le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L143-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L143-L146

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_take_le (w l : List ℕ) (n : ℕ) :
    countOccurrences w (l.take n) ≤ countOccurrences w l := by sorry
