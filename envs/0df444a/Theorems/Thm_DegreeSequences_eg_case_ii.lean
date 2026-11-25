-- Prove2me | Theorems.Thm_DegreeSequences_eg_case_ii
-- name    : DegreeSequences.eg_case_ii
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:06:01.13223+00:00
-- url     : https://prove2.me/theorems/0293d319-cffc-4c37-b5c5-709920b8f683
-- title:
--   Degree Sequences: eg case ii
-- statement:
--   The Degree Sequences construction uses the eg case ii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L549-L603
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L549-L603

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.eg_case_ii {n : ℕ} (d : Fin n → ℕ) (hEG : ∀ k ≤ n, ∑ i with i.val < k, d i ≤
      k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k)
    (t p : Fin n) (htp : t < p) (k : ℕ) (hkt : k ≤ t.val) (hLk : ∑ i with i.val < k, d i = k * d t)
    (htop : ∀ i ≤ t, d i = d t) (hp1 : 1 ≤ d p) (h1 : k < d t) (h2 : d p ≤ k) :
    ∑ i with i.val < k, d i + 1 ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by sorry
