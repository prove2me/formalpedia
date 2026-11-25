-- Prove2me | Theorems.Thm_DegreeSequences_degree_eq_sum_ite
-- name    : DegreeSequences.degree_eq_sum_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:37:04.579982+00:00
-- url     : https://prove2.me/theorems/6b7fec73-d7e5-4076-b556-b9c7d034b188
-- title:
--   Degree Sequences: degree eq sum ite
-- statement:
--   The Degree Sequences construction uses the degree eq sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L40-L42
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L40-L42

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.degree_eq_sum_ite {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ w, if G.Adj v w then 1 else 0 := by sorry
