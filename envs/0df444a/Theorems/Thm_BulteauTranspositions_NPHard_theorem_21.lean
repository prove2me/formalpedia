-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_theorem_21
-- name    : BulteauTranspositions.NPHard.theorem_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:55:18.702428+00:00
-- url     : https://prove2.me/theorems/cc0d464d-76b5-4145-9135-6ed8fcdf05c1
-- title:
--   Theorem 21 — Sorting by Transpositions is NP-hard
-- statement:
--   The Sorting by Transpositions decision problem is NP-hard. For every finite nonempty alphabet A and every language L in NP over A, there is a polynomial-time many-one reduction from L to the language of all valid encoded pairs (π,k) with d_t(π)≤k. Permutations have arbitrary positive span and fix the two sentinels. Every legal block transposition is allowed. Invalid encodings, invalid permutations and negative budgets are outside the language. The assertion is unconditional: SAT-completeness is an existing Open external dependency, not a hypothesis of this theorem.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: NP-hardness of the sorting decision problem → every NP language over every finite nonempty alphabet has a CookPvsNP.PolyReducible map to the sorting language; reason: this is ordinary polynomial-time many-one NP-hardness, including real Turing-machine running time and membership equivalence for every input word
--   - encoding: a permutation and an integer budget → a sign bit, self-delimiting binary n and budget magnitude, and all n+1 permutation entries; reason: the paper leaves bit syntax implicit; this is an unambiguous explicit encoding of every source input with logarithmic budget length
--   - encoding: d_t(π)≤k → existence of an actual sorting sequence of length at most the signed budget; reason: every valid permutation is sortable and its minimum sequence length is attained; the two predicates agree, including k<0 and zero moves
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Theorem 21, printed p. 34 = PDF p. 34; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Encoding

namespace BulteauTranspositions.NPHard

theorem theorem_21 :
    ∀ (A : Type) [Fintype A] [Nonempty A] (L : CookPvsNP.Lang A),
      L ∈ CookPvsNP.NP A → CookPvsNP.PolyReducible L sortingLanguage := by sorry

end BulteauTranspositions.NPHard
