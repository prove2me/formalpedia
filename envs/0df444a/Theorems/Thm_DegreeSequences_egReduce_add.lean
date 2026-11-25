-- Prove2me | Theorems.Thm_DegreeSequences_egReduce_add
-- name    : DegreeSequences.egReduce_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:37:15.235333+00:00
-- url     : https://prove2.me/theorems/3fc1835a-e277-4f3f-afd4-cdf2ce58f4b5
-- title:
--   Degree Sequences: eg Reduce add
-- statement:
--   The Degree Sequences construction uses the eg Reduce add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L463-L471
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L463-L471

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.egReduce_add {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (i : Fin n) :
    d i = egReduce d t p i + (if i = t then 1 else 0) + (if i = p then 1 else 0) := by sorry
