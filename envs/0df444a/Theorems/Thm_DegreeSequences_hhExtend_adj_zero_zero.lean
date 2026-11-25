-- Prove2me | Theorems.Thm_DegreeSequences_hhExtend_adj_zero_zero
-- name    : DegreeSequences.hhExtend_adj_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:46:48.884807+00:00
-- url     : https://prove2.me/theorems/4762a0bf-b6f9-4e53-969d-c5129c9f3bae
-- title:
--   Degree Sequences: hh Extend adj zero zero
-- statement:
--   The Degree Sequences construction uses the hh Extend adj zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L123-L124
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L123-L124

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.hhExtend_adj_zero_zero {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m)) :
    ¬ (hhExtend d H).Adj 0 0 := by sorry
