-- Prove2me | Theorems.Thm_DegreeSequences_exists_switch
-- name    : DegreeSequences.exists_switch
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:47:07.256843+00:00
-- url     : https://prove2.me/theorems/e69c9834-cfb4-415a-8203-19193450ef64
-- title:
--   Degree Sequences: exists switch
-- statement:
--   The Degree Sequences construction uses the exists switch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L160-L236
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L160-L236

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.exists_switch {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a i k : V) (hai : a ≠ i) (hdeg : G.degree k ≤ G.degree i)
    (hai' : ¬ G.Adj a i) (hak : G.Adj a k) :
    ∃ (G' : SimpleGraph V) (_ : DecidableRel G'.Adj), (∀ v, G'.degree v = G.degree v) ∧
      ∀ v, (G'.Adj a v ↔ (v ≠ k ∧ G.Adj a v) ∨ v = i) := by sorry
