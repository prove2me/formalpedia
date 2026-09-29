-- Prove2me | Theorems.Thm_BlockCycleRotation_tsum_telescope_inv
-- name    : BlockCycleRotation.tsum_telescope_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:08.514089+00:00
-- url     : https://prove2.me/theorems/e74ae407-3961-4357-8e25-e6fd06a192f5
-- title:
--   tsum telescope inv
-- statement:
--   A supporting lemma of the formalization, declared as `tsum_telescope_inv`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L507-L555

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.tsum_telescope_inv {K : ℕ} (hK : 0 < K) :
    ∑' j : ℕ, (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) = 1 / (K : ℝ) := by sorry
