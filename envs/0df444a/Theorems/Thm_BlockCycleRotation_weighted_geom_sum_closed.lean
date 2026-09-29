-- Prove2me | Theorems.Thm_BlockCycleRotation_weighted_geom_sum_closed
-- name    : BlockCycleRotation.weighted_geom_sum_closed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:48.321071+00:00
-- url     : https://prove2.me/theorems/d1e70091-873f-4d9c-be75-1da65a2e2ee3
-- title:
--   weighted geom sum closed
-- statement:
--   A supporting lemma of the formalization, declared as `weighted_geom_sum_closed`.
--
--   In Blomer–Bux this is **Obs. 17**, “Obs. 17: weighted sum, paper's constants”. It is used in the proof of `norm_weighted_geom_sum_le_sharp`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 17. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L199-L218

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.weighted_geom_sum_closed {θ : ℝ} (hne : e θ ≠ 1) (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ((T - 1 : ℕ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)) / (e θ - 1) := by sorry
