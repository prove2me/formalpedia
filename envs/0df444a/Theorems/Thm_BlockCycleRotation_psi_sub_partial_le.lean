-- Prove2me | Theorems.Thm_BlockCycleRotation_psi_sub_partial_le
-- name    : BlockCycleRotation.psi_sub_partial_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:06.572105+00:00
-- url     : https://prove2.me/theorems/f4d9f052-1c86-4e12-bb54-cd1ec6487796
-- title:
--   The tail bound: `|ψ - ψ_N| ≤ 3·(2/3)^N` uniformly on `[0,1/2]`
-- statement:
--   The tail bound: `|ψ - ψ_N| ≤ 3·(2/3)^N` uniformly on `[0,1/2]`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proofs of `continuousAt_psi`, `psi_sub_psiBuf_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L564-L586

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psi_sub_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    |psi x - psiPartial N x| ≤ 3 * (2 / 3 : ℝ) ^ N := by sorry
