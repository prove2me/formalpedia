-- Prove2me | Theorems.Thm_BlockCycleRotation_psiBuf_antitone
-- name    : BlockCycleRotation.psiBuf_antitone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:31.183346+00:00
-- url     : https://prove2.me/theorems/3fb596bf-3da3-4593-9f47-eedf38843ac4
-- title:
--   Monotone in the buffer size
-- statement:
--   **Monotone in the buffer size** (the corollary's first item).
--
--   In Blomer–Bux this is **Corollary 6(1)**, “Monotone in the buffer size”. It is used in the proof of `muCost_antitone`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 6(1). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L197-L219

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psiBuf_antitone {β₁ β₂ x : ℝ} (h12 : β₁ ≤ β₂) (hβ : 0 < β₁) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) : psiBuf β₂ x ≤ psiBuf β₁ x := by sorry
