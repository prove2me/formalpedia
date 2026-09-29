-- Prove2me | Theorems.Thm_BlockCycleRotation_muCost_one
-- name    : BlockCycleRotation.muCost_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:45.039126+00:00
-- url     : https://prove2.me/theorems/5440c9a9-f6f9-4b21-bf13-d1cd327c3452
-- title:
--   Remark (buffered relative cost)
-- statement:
--   **Remark (buffered relative cost).** `f_β(ℓ) = μ(1, ℓ, β)`: the per-element cost with a buffer of relative size `β` is the continuous cost of the unit problem.
--
--   In Blomer–Bux this is **Remark 13**, “`f_β(ℓ) = μ(1,ℓ,β)`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 13. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L705-L710

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.muCost_one (l b : ℝ) : muCost 1 l b = fCostBuf b l := by sorry
