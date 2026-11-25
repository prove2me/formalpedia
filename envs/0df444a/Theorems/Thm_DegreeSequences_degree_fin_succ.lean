-- Prove2me | Theorems.Thm_DegreeSequences_degree_fin_succ
-- name    : DegreeSequences.degree_fin_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:36:55.188748+00:00
-- url     : https://prove2.me/theorems/7f9f9a8b-b947-5264-9b9e-78289b175d8d
-- title:
--   Degree Sequences: degree fin succ
-- statement:
--   The Degree Sequences construction uses the degree fin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L111-L114
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L111-L114

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.degree_fin_succ {m : ℕ} (G : SimpleGraph (Fin (m + 1))) [DecidableRel G.Adj]
    (v : Fin (m + 1)) :
    G.degree v = (if G.Adj v 0 then 1 else 0) + #{w : Fin m | G.Adj v w.succ} := by sorry
