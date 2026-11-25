-- Prove2me | Theorems.Thm_DegreeSequences_egReduce_EG
-- name    : DegreeSequences.egReduce_EG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:06:21.459426+00:00
-- url     : https://prove2.me/theorems/0783cd19-9d5c-4f38-bf50-423d8e7559de
-- title:
--   Degree Sequences: eg Reduce EG
-- statement:
--   The Degree Sequences construction uses the eg Reduce EG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L606-L635
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L606-L635

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.egReduce_EG {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) (hev : Even (∑ i, d i))
    (hEG : ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k)
    (t p : Fin n) (htp : t < p) (hp1 : 1 ≤ d p) (htop : ∀ i ≤ t, d i = d t) :
    ∀ k ≤ n, ∑ i with i.val < k, egReduce d t p i ≤
      k * (k - 1) + ∑ i with k ≤ i.val, min (egReduce d t p i) k := by sorry
