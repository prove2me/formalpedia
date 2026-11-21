-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_append_le
-- name    : Champernowne.countOccurrences_append_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:30.611152+00:00
-- url     : https://prove2.me/theorems/f14c43be-97b2-4437-9144-cd60f6a8b18f
-- title:
--   Champernowne: count Occurrences append le
-- statement:
--   The seam bound with the word length as an upper bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L96-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L96-L100

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_append_le (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b + w.length := by sorry
