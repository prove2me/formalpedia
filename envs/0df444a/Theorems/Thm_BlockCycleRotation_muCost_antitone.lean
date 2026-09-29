-- Prove2me | Theorems.Thm_BlockCycleRotation_muCost_antitone
-- name    : BlockCycleRotation.muCost_antitone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:16.610049+00:00
-- url     : https://prove2.me/theorems/e4f6dee1-f805-4e48-be88-f32ea61bc72b
-- title:
--   Corollary, item 1: `μ` decreases in the buffer size
-- statement:
--   **Corollary, item 1: `μ` decreases in the buffer size.**
--
--   In Blomer–Bux this is **Corollary 6(1)**, “Corollary 6(1): `μ` decreases in `β`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 6(1). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L523-L534

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.muCost_antitone {N l b₁ b₂ : ℝ} (hN : 0 < N) (hb : 0 < b₁) (h12 : b₁ ≤ b₂)
    (hl0 : 0 ≤ l) (hl : 2 * l ≤ N) : muCost N l b₂ ≤ muCost N l b₁ := by sorry
