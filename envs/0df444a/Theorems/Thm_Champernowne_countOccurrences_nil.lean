-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_nil
-- name    : Champernowne.countOccurrences_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:35:19.25918+00:00
-- url     : https://prove2.me/theorems/438e4511-bee2-4bad-827f-514c4793f54f
-- title:
--   Champernowne: count Occurrences nil
-- statement:
--   The Champernowne construction uses the count Occurrences nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L39-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L39-L42

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

theorem Champernowne.countOccurrences_nil {w : List ℕ} (hw : w ≠ []) :
    countOccurrences w [] = 0 := by sorry
