-- Prove2me | Theorems.Thm_BlockCycleRotation_psiPartial_le_two
-- name    : BlockCycleRotation.psiPartial_le_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:46.372765+00:00
-- url     : https://prove2.me/theorems/df59c87d-93b4-44e0-b7e6-60cb811560c7
-- title:
--   `ψ_N ≤ 2` for every partial sum
-- statement:
--   **`ψ_N ≤ 2` for every partial sum**, by induction along the recursion.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L501-L524

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psiPartial_le_two : ∀ (N : ℕ) {x : ℝ}, 0 ≤ x → x ≤ 1 / 2 → psiPartial N x ≤ 2 := by sorry
