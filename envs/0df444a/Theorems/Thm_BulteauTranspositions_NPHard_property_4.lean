-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_4
-- name    : BulteauTranspositions.NPHard.property_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:19.672099+00:00
-- url     : https://prove2.me/theorems/3042dec1-503d-48fb-bf0d-59257ac958ba
-- title:
--   Property 4 — breakpoint lower bound
-- statement:
--   For every sentinel permutation π on {0,…,n}, the transposition distance satisfies d_t(π)≥d_b(π)/3. Division is exact, so in particular five breakpoints require at least two moves.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: the finite minimum number of sorting transpositions → the infimum of actual sequence lengths in the extended natural numbers; reason: legal sentinel permutations are sortable by adjacent single-entry block exchanges; the infimum is attained and finite on the entire source domain, while an empty feasible set never defaults to zero
--   - encoding: d_t≥d_b/3 → d_b≤3d_t; reason: multiplying by three preserves the exact bound; no floor division is used
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 4, printed p. 3 = PDF p. 3; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Sorting

namespace BulteauTranspositions.NPHard

theorem property_4 (n : ℕ) (p : ℕ → ℕ) (hp : IsPermutation n p) :
    (breakpoints n p : ℕ∞) ≤ 3 * distance n p := by sorry

end BulteauTranspositions.NPHard
