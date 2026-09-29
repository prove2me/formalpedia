-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_split_eq_sum_quadruples
-- name    : BlockCycleRotation.sum_split_eq_sum_quadruples
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:12.21274+00:00
-- url     : https://prove2.me/theorems/d10b1ab4-3592-4397-9bda-8df198fd068a
-- title:
--   The reindexing of (eq. heilbron)
-- statement:
--   **The reindexing of (eq. heilbron).**
--
--   In Blomer–Bux this is **§4**, “Reindexing by quadruples”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L832-L886

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_split_eq_sum_quadruples (n : ℕ) :
    ∑ k ∈ shifts n, ∑ j ∈ Finset.Ico 1 (cf n k).length, K ((cf n k).take j)
      = ∑ q ∈ quadruples n, q.1 := by sorry
