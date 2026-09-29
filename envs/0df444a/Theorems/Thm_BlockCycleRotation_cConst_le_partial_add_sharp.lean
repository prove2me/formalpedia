-- Prove2me | Theorems.Thm_BlockCycleRotation_cConst_le_partial_add_sharp
-- name    : BlockCycleRotation.cConst_le_partial_add_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:33.256636+00:00
-- url     : https://prove2.me/theorems/787cf4af-4dfa-4827-9f5e-d515b2f72cf2
-- title:
--   The sharper tail bound
-- statement:
--   **The sharper tail bound.** Truncating at `a ≤ N` loses at most `1/N`.
--
--   In Blomer–Bux this is **§4**, “Sharper `cTerm ≤ 1/a³`, tail `≤ 1/N`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Bound.lean#L49-L75

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cConst_le_partial_add_sharp {N : ℕ} (hN : 0 < N) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      + 1 / (N : ℝ) := by sorry
