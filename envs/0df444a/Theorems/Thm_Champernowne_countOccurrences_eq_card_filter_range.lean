-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_eq_card_filter_range
-- name    : Champernowne.countOccurrences_eq_card_filter_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:34:49.413177+00:00
-- url     : https://prove2.me/theorems/55625617-9a78-4bde-8e97-6cdfac99d454
-- title:
--   Champernowne: count Occurrences eq card filter range
-- statement:
--   `countOccurrences` counts window start positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L93-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L93-L105

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_eq_card_filter_range (w l : List ℕ) :
    countOccurrences w l
      = ((Finset.range (l.length + 1)).filter
          (fun j => w.isPrefixOf (l.drop j))).card := by sorry
