-- Prove2me | Theorems.Thm_DegreeSequences_degree_editGraph
-- name    : DegreeSequences.degree_editGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:36:47.250624+00:00
-- url     : https://prove2.me/theorems/4be773e6-3731-51cf-a095-2d009b25ce8c
-- title:
--   Degree Sequences: degree edit Graph
-- statement:
--   The Degree Sequences construction uses the degree edit Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L93-L108
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L93-L108

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.degree_editGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R A : Finset (Sym2 V)) [DecidableRel (editGraph G R A).Adj]
    (hR : ∀ e ∈ R, e ∈ G.edgeSet) (hA : ∀ e ∈ A, e ∉ G.edgeSet ∧ ¬ e.IsDiag) (v : V) :
    (editGraph G R A).degree v + ∑ e ∈ R, (if v ∈ e then 1 else 0) =
      G.degree v + ∑ e ∈ A, (if v ∈ e then 1 else 0) := by sorry
