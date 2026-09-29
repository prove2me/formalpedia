-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_weighted_geom_sum_le_sharp
-- name    : BlockCycleRotation.norm_weighted_geom_sum_le_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:35.359483+00:00
-- url     : https://prove2.me/theorems/81645b7f-06fe-492b-a921-61b94d7236cf
-- title:
--   Observation 17, weighted sum, in the paper's sharp form
-- statement:
--   **Observation 17, weighted sum, in the paper's sharp form.** For `0 < |θ| ≤ π`, `‖∑_{1 ≤ j < T} j · e(jθ)‖ ≤ π²/(2θ²) + (T-1)·π/(2|θ|)`.
--
--   In Blomer–Bux this is **Obs. 17**, “Obs. 17: weighted sum, paper's constants”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 17. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L220-L285

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_weighted_geom_sum_le_sharp {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖
      ≤ π ^ 2 / (2 * θ ^ 2) + (T - 1 : ℕ) * π / (2 * |θ|) := by sorry
