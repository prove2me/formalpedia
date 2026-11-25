-- Prove2me | Theorems.Thm_DegreeSequences_egReduce_sum_lt
-- name    : DegreeSequences.egReduce_sum_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:37:19.35513+00:00
-- url     : https://prove2.me/theorems/ca96e3b0-fb74-470f-be7f-d9ec9e569a25
-- title:
--   Degree Sequences: eg Reduce sum lt
-- statement:
--   The Degree Sequences construction uses the eg Reduce sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L494-L499
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L494-L499

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.egReduce_sum_lt {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (F : Finset (Fin n)) :
    ∑ i ∈ F, d i = ∑ i ∈ F, egReduce d t p i + (if t ∈ F then 1 else 0) +
      (if p ∈ F then 1 else 0) := by sorry
