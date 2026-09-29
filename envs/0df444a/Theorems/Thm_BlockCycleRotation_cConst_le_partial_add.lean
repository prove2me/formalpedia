-- Prove2me | Theorems.Thm_BlockCycleRotation_cConst_le_partial_add
-- name    : BlockCycleRotation.cConst_le_partial_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:30.137721+00:00
-- url     : https://prove2.me/theorems/087af24d-7701-43d6-a511-e27479bfb756
-- title:
--   The tail bound for `C`
-- statement:
--   **The tail bound for `C`.** Truncating the series at `a ≤ N` loses at most `3/(2N)`.
--
--   In Blomer–Bux this is **Lemma 19**, “Truncation error for `C`”. It is used in the proof of `cConst_le_bulk_add`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L213-L253

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cConst_le_partial_add {N : ℕ} (hN : 0 < N) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      + 3 / (2 * (N : ℝ)) := by sorry
