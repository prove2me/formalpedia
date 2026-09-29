-- Prove2me | Theorems.Thm_BlockCycleRotation_seg_succ_prime
-- name    : BlockCycleRotation.seg_succ_prime
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:41.437175+00:00
-- url     : https://prove2.me/theorems/2e1fff29-fe6f-43c3-b998-7187882fe861
-- title:
--   The one-step ratio of segments is `{1/Inⁱ(x)}`
-- statement:
--   The one-step ratio of segments is `{1/Inⁱ(x)}`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `seg_add_two_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L252-L264

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.seg_succ_prime (x : ℝ) (i : ℕ) :
    seg x (i + 1) = seg x i * Int.fract (1 / Inn^[i] x) := by sorry
