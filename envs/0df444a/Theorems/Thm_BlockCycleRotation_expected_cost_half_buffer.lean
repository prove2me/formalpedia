-- Prove2me | Theorems.Thm_BlockCycleRotation_expected_cost_half_buffer
-- name    : BlockCycleRotation.expected_cost_half_buffer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:27.055553+00:00
-- url     : https://prove2.me/theorems/6e5c91a3-6f55-4f0b-a366-ee7d7681a45b
-- title:
--   The figure's `1.25`
-- statement:
--   **The figure's `1.25`.** With a buffer of half the array, the expected cost is `5/4` moves per element.
--
--   In Blomer–Bux this is **Fig. 6 caption**, “Figure's `1.25` at a 50% buffer”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Fig. 6 caption. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L556-L567

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.expected_cost_half_buffer :
    2 * ∫ x in (0 : ℝ)..(1 / 2), fCostBuf (1 / 2) x = 5 / 4 := by sorry
