-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_6
-- name    : BulteauTranspositions.NPHard.property_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:50.983298+00:00
-- url     : https://prove2.me/theorems/66b2119d-cf1b-4023-8a59-f4e7a8d4ad36
-- title:
--   Property 6 — equivalence identifies all breakpoints
-- statement:
--   Let I=(Σ,T,ψ) be a 3DT-instance with domain L, and let π be an equivalent sentinel permutation of the same span. Then d_b(π)=|L|=3|T|. Both equalities are included.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 6, printed p. 7 = PDF p. 7; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace BulteauTranspositions.NPHard

theorem property_6 (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) :
    breakpoints I.span p = I.domain.card ∧ I.domain.card = 3 * I.triples.length := by sorry

end BulteauTranspositions.NPHard
