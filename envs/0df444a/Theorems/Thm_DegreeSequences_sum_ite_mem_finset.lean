-- Prove2me | Theorems.Thm_DegreeSequences_sum_ite_mem_finset
-- name    : DegreeSequences.sum_ite_mem_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:46:25.486125+00:00
-- url     : https://prove2.me/theorems/5b911c97-0edc-4958-afc7-0d45f7bcca35
-- title:
--   Degree Sequences: sum ite mem finset
-- statement:
--   The Degree Sequences construction uses the sum ite mem finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L83-L91
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L83-L91

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.sum_ite_mem_finset {V : Type*} [Fintype V] [DecidableEq V] (v : V) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, ¬ e.IsDiag) :
    (∑ w, if s(v, w) ∈ R then 1 else 0) = ∑ e ∈ R, if v ∈ e then 1 else 0 := by sorry
