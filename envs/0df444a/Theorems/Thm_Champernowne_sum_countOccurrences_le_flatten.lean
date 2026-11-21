-- Prove2me | Theorems.Thm_Champernowne_sum_countOccurrences_le_flatten
-- name    : Champernowne.sum_countOccurrences_le_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:14.151281+00:00
-- url     : https://prove2.me/theorems/4c530f25-1111-4583-861f-78e36d5037b3
-- title:
--   Champernowne: sum count Occurrences le flatten
-- statement:
--   Per-block occurrences survive flattening.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L170-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L170-L181

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_countOccurrences_le_flatten {w : List ℕ} (hw : w ≠ [])
    (L : List (List ℕ)) :
    (L.map (countOccurrences w)).sum ≤ countOccurrences w L.flatten := by sorry
