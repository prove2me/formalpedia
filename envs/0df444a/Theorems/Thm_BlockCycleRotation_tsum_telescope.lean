-- Prove2me | Theorems.Thm_BlockCycleRotation_tsum_telescope
-- name    : BlockCycleRotation.tsum_telescope
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:07.026508+00:00
-- url     : https://prove2.me/theorems/6523dcca-79c6-4fe7-8209-0a8beda27feb
-- title:
--   The telescoping series `∑_j [1/(j+1) - 1/(j+n+1)]` sums to `H_n`
-- statement:
--   The telescoping series `∑_j [1/(j+1) - 1/(j+n+1)]` sums to `H_n`.
--
--   In Blomer–Bux this is **Remark 21**, “Telescoping `∑_k [1/k − 1/(n+k)] = H_n`”. It is used in the proof of `qTerm_row`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L391-L431

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.tsum_telescope (n : ℕ) :
    ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by sorry
