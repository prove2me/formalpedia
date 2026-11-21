-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_cons
-- name    : Champernowne.countOccurrences_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:34:46.686993+00:00
-- url     : https://prove2.me/theorems/b718b933-0a3d-4136-baeb-72032fa5f0c0
-- title:
--   Champernowne: count Occurrences cons
-- statement:
--   The Champernowne construction uses the count Occurrences cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L30-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L30-L33

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

theorem Champernowne.countOccurrences_cons (w l : List ℕ) (x : ℕ) :
    countOccurrences w (x :: l)
      = countOccurrences w l + (if w.isPrefixOf (x :: l) then 1 else 0) := by sorry
