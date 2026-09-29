-- Prove2me | Theorems.Thm_BlockCycleRotation_seg_add_two_le
-- name    : BlockCycleRotation.seg_add_two_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:50.803635+00:00
-- url     : https://prove2.me/theorems/2f8e9eb8-f538-483b-9d6e-1506ee72568e
-- title:
--   Segments halve every two steps
-- statement:
--   For $0 \le x \le \tfrac12$ and every $i$,
--   $$\mathrm{seg}(x,i+2) \le \tfrac12\,\mathrm{seg}(x,i).$$
--
--   The geometric decay driving every convergence argument about $\psi$: two steps of the recursion at least halve the current segment, so the series defining $\psi$ converges geometrically and the recursion depth needed for a given accuracy is logarithmic. This is what the continuity proof of Theorem 7 rests on.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L297-L308

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.seg_add_two_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x (i + 2) ≤ 1 / 2 * seg x i := by sorry
