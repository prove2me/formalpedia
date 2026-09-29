-- Prove2me | Theorems.Thm_BlockCycleRotation_tsum_gTerm_le_partial
-- name    : BlockCycleRotation.tsum_gTerm_le_partial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:54.690285+00:00
-- url     : https://prove2.me/theorems/59f66117-3cef-4c5b-b93e-dd63d9d2e57a
-- title:
--   Truncating the all-pairs sum at `a ≤ N` loses at most `5/(8N)`
-- statement:
--   **Truncating the all-pairs sum at `a ≤ N` loses at most `5/(8N)`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `cConst_le_seventeen_eightieths`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L194-L234

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.tsum_gTerm_le_partial {N : ℕ} (hN : 0 < N) :
    ∑' p, gTerm p
      ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        + 5 / (8 * (N : ℝ)) := by sorry
