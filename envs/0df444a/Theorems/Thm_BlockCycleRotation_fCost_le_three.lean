-- Prove2me | Theorems.Thm_BlockCycleRotation_fCost_le_three
-- name    : BlockCycleRotation.fCost_le_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:56.697671+00:00
-- url     : https://prove2.me/theorems/1f3d9215-a3cd-49fe-aa92-4f27c5ebb6c9
-- title:
--   `f ≤ 3`:
-- statement:
--   **`f ≤ 3`:** the algorithm uses at most three moves per element.
--
--   In Blomer–Bux this is **Observation 5**, “`μ(N,ℓ,β) ≤ 3N`, i.e. `f ≤ 3`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Observation 5. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L538-L546

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.fCost_le_three {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fCost x ≤ 3 := by sorry
