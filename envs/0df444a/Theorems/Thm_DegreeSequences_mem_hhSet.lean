-- Prove2me | Theorems.Thm_DegreeSequences_mem_hhSet
-- name    : DegreeSequences.mem_hhSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:36:54.671397+00:00
-- url     : https://prove2.me/theorems/2f9099ee-1dab-5249-9cd5-60cd4b989bf3
-- title:
--   Degree Sequences: mem hh Set
-- statement:
--   The Degree Sequences construction uses the mem hh Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L243-L245
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L243-L245

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.mem_hhSet {m : ℕ} (d : Fin (m + 1) → ℕ) (v : Fin (m + 1)) :
    v ∈ hhSet d ↔ v ≠ 0 ∧ v.val < d 0 + 1 := by sorry
