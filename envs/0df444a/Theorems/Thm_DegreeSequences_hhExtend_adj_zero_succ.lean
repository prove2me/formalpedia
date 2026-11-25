-- Prove2me | Theorems.Thm_DegreeSequences_hhExtend_adj_zero_succ
-- name    : DegreeSequences.hhExtend_adj_zero_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:47:16.971088+00:00
-- url     : https://prove2.me/theorems/f7c783c4-6c41-4f42-9fe2-8ab29dc2604f
-- title:
--   Degree Sequences: hh Extend adj zero succ
-- statement:
--   The Degree Sequences construction uses the hh Extend adj zero succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L126-L128
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L126-L128

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.hhExtend_adj_zero_succ {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m))
    (j : Fin m) : (hhExtend d H).Adj 0 j.succ ↔ j.val < d 0 := by sorry
