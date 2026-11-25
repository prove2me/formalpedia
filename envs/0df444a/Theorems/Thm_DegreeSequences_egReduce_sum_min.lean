-- Prove2me | Theorems.Thm_DegreeSequences_egReduce_sum_min
-- name    : DegreeSequences.egReduce_sum_min
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:57:13.363613+00:00
-- url     : https://prove2.me/theorems/7b1dcf65-eb6d-5ca8-a167-64300969b559
-- title:
--   Degree Sequences: eg Reduce sum min
-- statement:
--   The Degree Sequences construction uses the eg Reduce sum min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L501-L517
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L501-L517

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.egReduce_sum_min {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (k : ℕ) (F : Finset (Fin n)) :
    ∑ i ∈ F, min (d i) k = ∑ i ∈ F, min (egReduce d t p i) k +
      (if t ∈ F then (if d t ≤ k then 1 else 0) else 0) +
      (if p ∈ F then (if d p ≤ k then 1 else 0) else 0) := by sorry
