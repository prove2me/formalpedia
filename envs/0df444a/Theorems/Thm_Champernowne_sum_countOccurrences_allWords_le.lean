-- Prove2me | Theorems.Thm_Champernowne_sum_countOccurrences_allWords_le
-- name    : Champernowne.sum_countOccurrences_allWords_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:32.475229+00:00
-- url     : https://prove2.me/theorems/071a3e34-30a3-4bb1-a21a-c1216efe5594
-- title:
--   Champernowne: sum count Occurrences all Words le
-- statement:
--   Window pigeonhole: a window position matches at most one length-`k`
--   word, so over ALL length-`k` words the occurrence counts total at most the
--   number of window start positions. This single inequality replaces the
--   entire upper-bound counting chain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L168-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L168-L197

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

theorem Champernowne.sum_countOccurrences_allWords_le (b k : ℕ) (l : List ℕ) :
    ∑ v ∈ allWords b k, countOccurrences v l ≤ l.length + 1 := by sorry
