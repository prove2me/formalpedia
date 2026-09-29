-- Prove2me | Theorems.Thm_BlockCycleRotation_tsum_gTerm_eq
-- name    : BlockCycleRotation.tsum_gTerm_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:03.970363+00:00
-- url     : https://prove2.me/theorems/438149f2-aedc-48e7-9859-7950b0e12916
-- title:
--   The `ζ(3)` unfolding
-- statement:
--   **The `ζ(3)` unfolding.**
--
--   In Blomer–Bux this is **Remark 21**, “`ζ(3)` removes the coprimality”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L242-L304

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.tsum_gTerm_eq : ∑' p : ℕ × ℕ, gTerm p = ∑' q : ℕ × (ℕ × ℕ), uTerm q.1 * cTerm q.2 := by sorry
