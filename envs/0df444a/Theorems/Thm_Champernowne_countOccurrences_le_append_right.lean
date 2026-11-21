-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_le_append_right
-- name    : Champernowne.countOccurrences_le_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:29.768686+00:00
-- url     : https://prove2.me/theorems/86d6f00b-d7c7-4e21-b39c-d936a1cfbda2
-- title:
--   Champernowne: count Occurrences le append right
-- statement:
--   The Champernowne construction uses the count Occurrences le append right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L118-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L118-L141

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_le_append_right (w a b : List ℕ) :
    countOccurrences w a ≤ countOccurrences w (a ++ b) := by sorry
