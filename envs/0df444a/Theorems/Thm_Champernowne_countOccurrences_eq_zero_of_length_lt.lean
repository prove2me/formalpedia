-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_eq_zero_of_length_lt
-- name    : Champernowne.countOccurrences_eq_zero_of_length_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:16.189185+00:00
-- url     : https://prove2.me/theorems/ae885737-7c73-4d44-8a45-a6f5358e5642
-- title:
--   Champernowne: count Occurrences eq zero of length lt
-- statement:
--   No occurrences of `w` in a list shorter than `w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L184-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L184-L193

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_eq_zero_of_length_lt {w l : List ℕ}
    (h : l.length < w.length) : countOccurrences w l = 0 := by sorry
