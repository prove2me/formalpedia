-- Prove2me | Theorems.Thm_BlockCycleRotation_gTerm_row_ge
-- name    : BlockCycleRotation.gTerm_row_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:18.609509+00:00
-- url     : https://prove2.me/theorems/76c76dc1-6cb1-469f-b3a4-ae925688c28f
-- title:
--   gTerm row ge
-- statement:
--   A supporting lemma of the formalization, declared as `gTerm_row_ge`.
--
--   In Blomer–Bux this is **§4**, “Row bound from below `≥ 5(a−1)/(9a³)`”. It is used in the proof of `tsum_gTerm_ge`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L464-L503

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.gTerm_row_ge {a : ℕ} (ha : 61 ≤ a) :
    (54 / 100 : ℝ) / (a : ℝ) ^ 2 ≤ ∑ a' ∈ Finset.range a, gTerm (a, a') := by sorry
