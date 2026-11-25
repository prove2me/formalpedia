-- Prove2me | Theorems.Thm_DegreeSequences_eg_necessary
-- name    : DegreeSequences.eg_necessary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:56:49.143606+00:00
-- url     : https://prove2.me/theorems/38ac68a3-dea5-4317-b48a-e9af64da26ab
-- title:
--   Degree Sequences: eg necessary
-- statement:
--   The Degree Sequences construction uses the eg necessary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L335-L377
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L335-L377

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.eg_necessary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    ∑ i with i.val < k, G.degree i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (G.degree i) k := by sorry
