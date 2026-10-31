-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_theorem_20
-- name    : BulteauTranspositions.NPHard.theorem_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:57:29.152982+00:00
-- url     : https://prove2.me/theorems/be5e3ad8-8fbb-4b9a-b629-a180a29393c0
-- title:
--   Theorem 20 — polynomial construction of an equivalent permutation
-- statement:
--   For every assembling of basic blocks of span n, the permutation π_I computed by the four explicit rows of Table 1 is a bijection of {0,…,n}, fixes both sentinels, and is equivalent to I. One Turing machine computes its entire list of values within n^k+k steps, for a single exponent k independent of the assembling. Assemblings may have any legal number and arrangement of the four gate types and any finite symbol names. No equivalent permutation is assumed to exist.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: a construction computable in polynomial time → one finite-alphabet one-tape Turing machine and exponent, uniform over every legal input, with bound size^k+k; reason: this is the published Cook machine model with actual step counting, not an output-length bound; compact syntax has polynomial length in the source size
--   - encoding: an arbitrary assembling (I,B) → a well-wired gate list and any instance obtained by injective relabeling of its concatenated words; reason: every Definition 14 assembling has exactly this presentation; natural-number gate names impose no bound on span
--   - encoding: existence of π_I, constructed explicitly in the proof → the concrete Table 1 value list is asserted to be a permutation equivalent to I; reason: the same witness is chosen as in the proof; R/P label typos change no equation
--   - encoding: input size n and output permutation → gate kinds and compact port numbers as input, the full binary list π(0),…,π(n) as output; reason: the annotated assembling has polynomial code length in n; the machine bound is stated directly in n, not merely in output length
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Theorem 20, printed p. 31 = PDF p. 31; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_PermutationConstruction

namespace BulteauTranspositions.NPHard

theorem theorem_20 :
    (∃ (Γ : Type) (_ : Fintype Γ) (ι : Bool ↪ Γ) (M : CookPvsNP.TM Γ) (k : ℕ),
      ∀ gs : List Gate, WellWired gs →
        let time := (assemblyWord gs).length ^ k + k
        M.HaltsWithin time ((encodeAssembly gs).map ι) ∧
        M.output (M.run time (M.init ((encodeAssembly gs).map ι))) =
          (encodeNats (permutationValues gs)).map (some ∘ ι)) ∧
    ∀ gs : List Gate, WellWired gs → ∀ (C : Context) (f : ℕ → ℕ),
      Relabels (assembly gs) C f →
      IsPermutation C.inst.span (constructedPermutation gs) ∧
      Equivalent C.inst (constructedPermutation gs) := by sorry

end BulteauTranspositions.NPHard
