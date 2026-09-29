-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_mul
-- name    : BlockCycleRotation.remSum_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:50:49.995292+00:00
-- url     : https://prove2.me/theorems/d63f9298-535d-4038-b1f5-433e582ca2a6
-- title:
--   The remainder sum scales
-- statement:
--   **The remainder sum scales.**
--
--   In Blomer–Bux this is **§4**, “Remainder sum scales”. It is used in the proof of `sum_remSum_allShifts`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Euclid.lean#L109-L124

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.remSum_mul : ∀ k n d : ℕ, remSum (d * n) (d * k) = d * remSum n k := by sorry
