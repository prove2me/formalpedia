-- Prove2me | Theorems.Thm_DegreeSequences_augment
-- name    : DegreeSequences.augment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:56:43.044606+00:00
-- url     : https://prove2.me/theorems/8724d52c-1546-5b20-a9d4-0ed114d49a8a
-- title:
--   Degree Sequences: augment
-- statement:
--   The Degree Sequences construction uses the augment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L382-L456
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L382-L456

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.augment {V : Type*} [Fintype V] [DecidableEq V] (G' : SimpleGraph V) [DecidableRel G'.Adj]
    (d : V → ℕ) (t p : V) (htp : t ≠ p) (hp1 : 1 ≤ d p)
    (hdeg : ∀ v, G'.degree v + (if v = t then 1 else 0) + (if v = p then 1 else 0) = d v)
    (hQ : d t ≤ #{x | x ≠ t ∧ d p ≤ d x}) :
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj), ∀ v, G.degree v = d v := by sorry
