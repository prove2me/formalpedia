-- Prove2me | Theorems.Thm_DegreeSequences_eg_sufficient
-- name    : DegreeSequences.eg_sufficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:06:13.967446+00:00
-- url     : https://prove2.me/theorems/66ee3ce3-f2f7-51c0-a703-a19df5d969c5
-- title:
--   Degree Sequences: eg sufficient
-- statement:
--   The Degree Sequences construction uses the eg sufficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L637-L730
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L637-L730

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.eg_sufficient {n : ℕ} (s : ℕ) : ∀ (d : Fin n → ℕ), ∑ i, d i = s → Antitone d →
    Even (∑ i, d i) →
    (∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k) →
    IsGraphic d := by sorry
