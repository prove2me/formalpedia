-- Prove2me | Theorems.Thm_BlockCycleRotation_K_tail_lt
-- name    : BlockCycleRotation.K_tail_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:53.353827+00:00
-- url     : https://prove2.me/theorems/616e8b17-6b38-4d9a-9820-36f78ba38f71
-- title:
--   Dropping the first entry strictly decreases the continuant
-- statement:
--   Dropping the first entry strictly decreases the continuant. This is the mirror image of `K_dropLast_lt`, via `K_reverse`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `K_tail_lt_prime`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L147-L160

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_tail_lt (l : List ℕ) (hlen : 2 ≤ l.length) (hpos : ∀ c ∈ l, 1 ≤ c) :
    K l.tail < K l := by sorry
