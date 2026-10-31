-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_theorem_9
-- name    : BulteauTranspositions.NPHard.theorem_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:53:13.215858+00:00
-- url     : https://prove2.me/theorems/2096ece0-9f11-4387-82b0-4cfc9df2117b
-- title:
--   Theorem 9 — collapsibility exactly attains the breakpoint bound
-- statement:
--   Let I=(Σ,T,ψ) be a 3DT-instance equivalent to a sentinel permutation π of the same span. Then I is 3DT-collapsible if and only if the entire chain d_t(π)=|T|=d_b(π)/3 holds. Empty triple sets and zero-step collapse are included.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: the finite minimum number of sorting transpositions → the infimum of actual sequence lengths in the extended natural numbers; reason: legal sentinel permutations are sortable by adjacent single-entry block exchanges; the infimum is attained and finite on the entire source domain, while an empty feasible set never defaults to zero
--   - encoding: d_t=|T|=d_b/3 → d_t=|T| and 3|T|=d_b; reason: both equalities and both implications are retained with exact integer arithmetic
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Theorem 9, printed p. 10 = PDF p. 10; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace BulteauTranspositions.NPHard

theorem theorem_9 (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) :
    Collapsible I ↔ distance I.span p = (I.triples.length : ℕ∞) ∧
      3 * I.triples.length = breakpoints I.span p := by sorry

end BulteauTranspositions.NPHard
