-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_lemma_8
-- name    : BulteauTranspositions.NPHard.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:50.449864+00:00
-- url     : https://prove2.me/theorems/1aa6a5a8-87e9-4f77-bf5d-1c6b385e94a9
-- title:
--   Lemma 8 — a three-breakpoint move comes from a well-ordered triple
-- statement:
--   Let I be a 3DT-instance equivalent to a sentinel permutation π. If a legal block transposition τ removes exactly three breakpoints, then there exists a well-ordered triple t in T whose associated transposition is τ.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: d_b(π∘τ)=d_b(π)−3 → d_b(π∘τ)+3=d_b(π); reason: the source means an exact drop of three in integers; natural subtraction would introduce spurious cases below three
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Lemma 8, printed p. 9 = PDF p. 9; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace BulteauTranspositions.NPHard

theorem lemma_8 (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) (c : Cut) (hc : c.Legal I.span)
    (hd : breakpoints I.span (applyMove p c) + 3 = breakpoints I.span p) :
    ∃ t ∈ I.triples, WellOrdered I t ∧ c.tau = (tripleCut I t).tau := by sorry

end BulteauTranspositions.NPHard
