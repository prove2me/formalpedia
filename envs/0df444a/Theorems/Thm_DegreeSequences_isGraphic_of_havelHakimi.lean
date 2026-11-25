-- Prove2me | Theorems.Thm_DegreeSequences_isGraphic_of_havelHakimi
-- name    : DegreeSequences.isGraphic_of_havelHakimi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:47:06.871557+00:00
-- url     : https://prove2.me/theorems/394828dc-2ce6-44d6-9639-83b72eae4996
-- title:
--   Degree Sequences: is Graphic of havel Hakimi
-- statement:
--   The Degree Sequences construction uses the is Graphic of havel Hakimi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L136-L157
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L136-L157

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.isGraphic_of_havelHakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (h0 : d 0 ≤ m)
    (hpos : ∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) (hH : IsGraphic (havelHakimi d)) :
    IsGraphic d := by sorry
