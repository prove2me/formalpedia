-- Prove2me | Theorems.Thm_BlockCycleRotation_gTerm_row_le
-- name    : BlockCycleRotation.gTerm_row_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:50.099098+00:00
-- url     : https://prove2.me/theorems/f99e84c5-18c6-49de-a137-5fc8184a658a
-- title:
--   `∑_{a'<a} gTerm ≤ 5/(8a²)`
-- statement:
--   **`∑_{a'<a} gTerm ≤ 5/(8a²)`.**
--
--   In Blomer–Bux this is **§4**, “Row bound `∑_{a'<a} gTerm ≤ 5/(8a²)`”. It is used in the proof of `tsum_gTerm_le_partial`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L141-L175

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.gTerm_row_le (a : ℕ) :
    ∑ a' ∈ Finset.range a, gTerm (a, a') ≤ 5 / (8 * (a : ℝ) ^ 2) := by sorry
