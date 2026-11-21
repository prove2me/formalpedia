-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_singleton
-- name    : Champernowne.countOccurrences_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:51.570656+00:00
-- url     : https://prove2.me/theorems/f0d6f533-d1f0-4f94-ae94-86b88a489199
-- title:
--   Champernowne: count Occurrences singleton
-- statement:
--   Sanity bridge to `List.count`: single-letter blocks are `List.count`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L29-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L29-L39

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_singleton (d : ℕ) (l : List ℕ) :
    countOccurrences [d] l = l.count d := by sorry
