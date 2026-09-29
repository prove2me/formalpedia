-- Prove2me | Theorems.Thm_BlockCycleRotation_psi_sub_psiBuf_le_linear
-- name    : BlockCycleRotation.psi_sub_psiBuf_le_linear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:52.232729+00:00
-- url     : https://prove2.me/theorems/b5c0a1aa-5c05-4b3c-88f0-d178bbc91da6
-- title:
--   `ψ - ψ_β ≤ 8β`
-- statement:
--   **`ψ - ψ_β ≤ 8β`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `tendsto_psiBuf`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L351-L369

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psi_sub_psiBuf_le_linear {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x - psiBuf β x ≤ 8 * β := by sorry
