-- Prove2me | Theorems.Thm_BlockCycleRotation_muCost_le_three_mul
-- name    : BlockCycleRotation.muCost_le_three_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:21.557014+00:00
-- url     : https://prove2.me/theorems/374a5988-4026-46d9-bbf2-38d73c01ecae
-- title:
--   The Observation `μ(N,ℓ,β) ≤ 3N`
-- statement:
--   **The Observation `μ(N,ℓ,β) ≤ 3N`.**
--
--   In Blomer–Bux this is **Observation 5**, “Observation `μ(N,ℓ,β) ≤ 3N`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Observation 5. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L510-L521

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.muCost_le_three_mul {N l b : ℝ} (hN : 0 < N) (hb : 0 < b) (hl0 : 0 ≤ l)
    (hl : 2 * l ≤ N) : muCost N l b ≤ 3 * N := by sorry
