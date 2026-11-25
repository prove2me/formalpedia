-- Prove2me | Theorems.Thm_DegreeSequences_egReduce_antitone
-- name    : DegreeSequences.egReduce_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:57:11.346302+00:00
-- url     : https://prove2.me/theorems/361729ae-43b8-438d-93e0-c27b20880643
-- title:
--   Degree Sequences: eg Reduce antitone
-- statement:
--   The Degree Sequences construction uses the eg Reduce antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L473-L492
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L473-L492

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.egReduce_antitone {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) (t p : Fin n) (htp : t < p)
    (hp1 : 1 ≤ d p) (hpz : ∀ i, p < i → d i = 0)
    (htmax : ∀ i, t < i → i < p → d i < d t) : Antitone (egReduce d t p) := by sorry
