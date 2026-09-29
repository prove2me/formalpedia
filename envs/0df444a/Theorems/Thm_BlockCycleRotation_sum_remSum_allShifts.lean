-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_remSum_allShifts
-- name    : BlockCycleRotation.sum_remSum_allShifts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:19.073189+00:00
-- url     : https://prove2.me/theorems/89e45479-907a-4203-8f15-fc7475ad59aa
-- title:
--   The remainder sums, aggregated over the gcd
-- statement:
--   The remainder sums, aggregated over the gcd.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L998-L1011

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_remSum_allShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = ∑ g ∈ n.divisors, g * ∑ k' ∈ shifts (n / g), remSum (n / g) k' := by sorry
