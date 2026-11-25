-- Prove2me | Theorems.Thm_DegreeSequences_eg_case_i
-- name    : DegreeSequences.eg_case_i
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:57:57.403647+00:00
-- url     : https://prove2.me/theorems/0393e464-6c2e-5e45-a165-bf7d42188396
-- title:
--   Degree Sequences: eg case i
-- statement:
--   The Degree Sequences construction uses the eg case i property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L519-L547
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L519-L547

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.eg_case_i {n : ℕ} (d : Fin n → ℕ) (hev : Even (∑ i, d i)) (t p : Fin n) (htp : t ≠ p)
    (hp1 : 1 ≤ d p) (k : ℕ) (hkt : k ≤ t.val) (hkp : k ≤ p.val) (hle : ∀ i, d i ≤ d t)
    (hLk : ∑ i with i.val < k, d i = k * d t) (h1 : d t ≤ k) :
    ∑ i with i.val < k, d i + 2 ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by sorry
