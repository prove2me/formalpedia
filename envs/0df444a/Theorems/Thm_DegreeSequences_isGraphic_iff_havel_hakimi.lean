-- Prove2me | Theorems.Thm_DegreeSequences_isGraphic_iff_havel_hakimi
-- name    : DegreeSequences.isGraphic_iff_havel_hakimi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:37:31.667546+00:00
-- url     : https://prove2.me/theorems/cb06f548-f97b-42f7-952b-db13e5f42022
-- title:
--   Degree Sequences: is Graphic iff havel hakimi
-- statement:
--   **Havel–Hakimi theorem (Havel 1955, Hakimi 1962).** A non-increasing sequence `d₀, …, d_m` is
--   graphic if and only if `d₀ ≤ m`, the terms `d₁, …, d_{d₀}` are positive, and its Havel–Hakimi
--   reduction is graphic.
--
--   Source: https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L752-L756
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean#L752-L756

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences

theorem DegreeSequences.isGraphic_iff_havel_hakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) := by sorry
