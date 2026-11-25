-- Prove2me | Theorems.Thm_DegreeSequences_sum_ite_sym2_eq
-- name    : DegreeSequences.sum_ite_sym2_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:46:04.397324+00:00
-- url     : https://prove2.me/theorems/3a5414b6-19ce-5088-853c-05d5f8619c1f
-- title:
--   Degree Sequences: sum ite sym2 eq
-- statement:
--   The Degree Sequences construction uses the sum ite sym2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L58-L81
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L58-L81

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.sum_ite_sym2_eq {V : Type*} [Fintype V] [DecidableEq V] (v : V) (e : Sym2 V)
    (he : ¬ e.IsDiag) :
    (∑ w, if s(v, w) = e then 1 else 0) = if v ∈ e then 1 else 0 := by sorry
