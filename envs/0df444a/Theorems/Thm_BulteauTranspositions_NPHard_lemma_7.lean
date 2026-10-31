-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_lemma_7
-- name    : BulteauTranspositions.NPHard.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:55.493982+00:00
-- url     : https://prove2.me/theorems/3cf94465-1d09-4fa7-857f-85009aa77681
-- title:
--   Lemma 7 — equivalence survives a 3DT-step
-- statement:
--   Let I be a 3DT-instance and π an equivalent sentinel permutation of the same span. If a well-ordered triple t=(a,b,c) yields a 3DT-step I→I′, then I′ is equivalent to π∘τ[t,ψ]. The step keeps the span, removes exactly that triple, and moves all surviving symbols by τ⁻¹.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Lemma 7, printed p. 8 = PDF p. 8; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace BulteauTranspositions.NPHard

theorem lemma_7 (I J : Instance) (t : Triple) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) (hs : Step I t J) :
    Equivalent J (applyMove p (tripleCut I t)) := by sorry

end BulteauTranspositions.NPHard
