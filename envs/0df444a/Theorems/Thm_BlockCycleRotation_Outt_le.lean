-- Prove2me | Theorems.Thm_BlockCycleRotation_Outt_le
-- name    : BlockCycleRotation.Outt_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:35.62716+00:00
-- url     : https://prove2.me/theorems/ea896cc9-0a14-4d4b-95cc-a6da2fcccb59
-- title:
--   `Out ≤ 2/3` on `[0,1/2]`
-- statement:
--   **`Out ≤ 2/3` on `[0,1/2]`.** With `m = ⌊1/x⌋ ≥ 2` one has `Out(x) = 1 - (m-1)x` and `x > 1/(m+1)`, so `Out(x) < 2/(m+1) ≤ 2/3`.
--
--   In Blomer–Bux this is **Observation 4**, “Relative recursion `In`, `Out`, and `Out ≤ 2/3`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Observation 4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L74-L94

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Outt x ≤ 2 / 3 := by sorry
