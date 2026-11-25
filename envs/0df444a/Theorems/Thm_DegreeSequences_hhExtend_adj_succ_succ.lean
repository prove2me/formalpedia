-- Prove2me | Theorems.Thm_DegreeSequences_hhExtend_adj_succ_succ
-- name    : DegreeSequences.hhExtend_adj_succ_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:47:06.096286+00:00
-- url     : https://prove2.me/theorems/fe3d4ddd-f025-4447-8dd6-51e91d51cfac
-- title:
--   Degree Sequences: hh Extend adj succ succ
-- statement:
--   The Degree Sequences construction uses the hh Extend adj succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L130-L134
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L130-L134

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.hhExtend_adj_succ_succ {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m))
    (j k : Fin m) : (hhExtend d H).Adj j.succ k.succ ↔ H.Adj j k := by sorry
