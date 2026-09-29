-- Prove2me | Theorems.Thm_BlockCycleRotation_fCostBuf_le_fCost
-- name    : BlockCycleRotation.fCostBuf_le_fCost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:43.473508+00:00
-- url     : https://prove2.me/theorems/20c6fc37-c6d2-44d5-b65e-cef9fbf26e5e
-- title:
--   The buffer never hurts
-- statement:
--   **The buffer never hurts**, for `f`.
--
--   In Blomer–Bux this is **Corollary 6(1)**, “The buffer never hurts, `f_β ≤ f`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 6(1). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L226-L230

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.fCostBuf_le_fCost {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    fCostBuf β x ≤ fCost x := by sorry
