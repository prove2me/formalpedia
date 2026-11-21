-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_le_cons
-- name    : Champernowne.countOccurrences_le_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:26.535508+00:00
-- url     : https://prove2.me/theorems/c5d7989b-ddcf-490a-bdd1-e8de5f3b6232
-- title:
--   Champernowne: count Occurrences le cons
-- statement:
--   The Champernowne construction uses the count Occurrences le cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L53-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L53-L56

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_le_cons (w l : List ℕ) (x : ℕ) :
    countOccurrences w l ≤ countOccurrences w (x :: l) := by sorry
