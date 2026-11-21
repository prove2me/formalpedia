-- Prove2me | Theorems.Thm_Champernowne_if_isPrefixOf_le_countOccurrences
-- name    : Champernowne.if_isPrefixOf_le_countOccurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:25.210189+00:00
-- url     : https://prove2.me/theorems/47f2a0db-a617-4675-8bd7-b43a779d5a07
-- title:
--   Champernowne: if is Prefix Of le count Occurrences
-- statement:
--   The whole-list window contributes to the count.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L111-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L111-L116

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.if_isPrefixOf_le_countOccurrences (w l : List ℕ) :
    (if w.isPrefixOf l then 1 else 0) ≤ countOccurrences w l := by sorry
