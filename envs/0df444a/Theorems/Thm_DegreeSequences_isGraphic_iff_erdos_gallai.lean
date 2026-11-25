-- Prove2me | Theorems.Thm_DegreeSequences_isGraphic_iff_erdos_gallai
-- name    : DegreeSequences.isGraphic_iff_erdos_gallai
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:37:23.240408+00:00
-- url     : https://prove2.me/theorems/6e618c87-c7b5-43b7-ae95-e2acaf758c9e
-- title:
--   Degree Sequences: is Graphic iff erdos gallai
-- statement:
--   **Erdős–Gallai theorem (1960).** A non-increasing sequence of natural numbers is the degree
--   sequence of a simple graph if and only if its sum is even and every initial segment satisfies the
--   Erdős–Gallai inequality.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L735-L747
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L735-L747

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.isGraphic_iff_erdos_gallai {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ Even (∑ i, d i) ∧
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by sorry
