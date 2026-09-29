-- Prove2me | Theorems.Thm_BlockCycleRotation_buffer_helps
-- name    : BlockCycleRotation.buffer_helps
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:06.587451+00:00
-- url     : https://prove2.me/theorems/2270c29f-9b37-45ee-85b9-140d84eec1e2
-- title:
--   A buffer helps even when no segment fits inside it
-- statement:
--   With buffer fraction $\beta = \tfrac14$ and rotation $x = \tfrac25$,
--   $$\tfrac14 < \tfrac25, \qquad \tfrac14 < 1-\tfrac25, \qquad f_\beta\left(\tfrac25\right) = 2, \qquad f\left(\tfrac25\right) = \tfrac{11}{5}.$$
--
--   The remark on buffering. Neither of the two segments fits into the buffer — both $\tfrac25$ and $\tfrac35$ exceed $\tfrac14$ — and yet the buffered cost $2$ is strictly below the unbuffered $11/5$. The example shows that the benefit of a buffer is not merely that it can hold a whole segment: it also shortens the recursion.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 13. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L439-L449

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.buffer_helps :
    (1 / 4 : ℝ) < 2 / 5 ∧ (1 / 4 : ℝ) < 1 - 2 / 5
      ∧ fCostBuf (1 / 4 : ℝ) (2 / 5 : ℝ) = 2 ∧ fCost (2 / 5 : ℝ) = 11 / 5 := by sorry
