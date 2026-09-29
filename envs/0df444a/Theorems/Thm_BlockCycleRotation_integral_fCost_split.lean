-- Prove2me | Theorems.Thm_BlockCycleRotation_integral_fCost_split
-- name    : BlockCycleRotation.integral_fCost_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:44.012697+00:00
-- url     : https://prove2.me/theorems/fad55298-27e2-4376-b348-73a30f66716f
-- title:
--   `∫₀¹ f = 2∫₀^{1/2} f`
-- statement:
--   **`∫₀¹ f = 2∫₀^{1/2} f`.**
--
--   In Blomer–Bux this is **Thm 9**, “`f(1−x) = f(x)`, `∫₀¹ = 2∫₀^{1/2}`”. It is used in the proof of `theorem10`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 9. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L1059-L1076

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.integral_fCost_split :
    ∫ x in (0 : ℝ)..1, fCost x = 2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x := by sorry
