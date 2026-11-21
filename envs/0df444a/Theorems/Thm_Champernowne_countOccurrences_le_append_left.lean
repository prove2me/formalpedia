-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_le_append_left
-- name    : Champernowne.countOccurrences_le_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:22.654675+00:00
-- url     : https://prove2.me/theorems/b6ea5b66-51fa-4aee-bb8f-c8339952d48e
-- title:
--   Champernowne: count Occurrences le append left
-- statement:
--   The Champernowne construction uses the count Occurrences le append left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L102-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L102-L108

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_le_append_left (w a b : List ℕ) :
    countOccurrences w b ≤ countOccurrences w (a ++ b) := by sorry
