-- Prove2me | Theorems.Thm_BlockCycleRotation_cost_le_muCost
-- name    : BlockCycleRotation.cost_le_muCost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:29.117668+00:00
-- url     : https://prove2.me/theorems/a5b3172f-f7cc-4225-bca8-505cd5717b92
-- title:
--   Corollary, item 3, unbuffered case
-- statement:
--   **Corollary, item 3, unbuffered case.** The actual move count is at most `μ(N,ℓ,0⁺) = N·f(ℓ/N)`; this is equation (relation).
--
--   In Blomer–Bux this is **Corollary 6(3)**, “Corollary 6(3), unbuffered limit”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 6(3). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L536-L542

import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.cost_le_muCost {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((algCost n k : ℕ) : ℝ) ≤ (n : ℝ) * fCost ((k : ℝ) / (n : ℝ)) := by sorry
