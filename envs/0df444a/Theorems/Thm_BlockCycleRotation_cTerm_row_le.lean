-- Prove2me | Theorems.Thm_BlockCycleRotation_cTerm_row_le
-- name    : BlockCycleRotation.cTerm_row_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:19.812812+00:00
-- url     : https://prove2.me/theorems/cb7769ca-9efc-4463-8266-8cc8661a9008
-- title:
--   The number of admissible `a'` for a given `a` is less than `a`, so the row sums are at most `3 / (2a²)`
-- statement:
--   The number of admissible `a'` for a given `a` is less than `a`, so the row sums are at most `3 / (2a²)`.
--
--   In Blomer–Bux this is **Eq. (const-c)**, “Constant `C` of eq. (const-c)”. It is used in the proof of `cConst_le_partial_add`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Eq. (const-c). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L53-L67

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cTerm_row_le (a : ℕ) :
    ∑ a' ∈ Finset.range a, cTerm (a, a') ≤ 3 / (2 * (a : ℝ) ^ 2) := by sorry
