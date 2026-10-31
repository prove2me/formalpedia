-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_theorem_19
-- name    : BulteauTranspositions.NPHard.theorem_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:55:52.096718+00:00
-- url     : https://prove2.me/theorems/df518b85-e55e-406e-bc5e-c2e839b2709c
-- title:
--   Theorem 19 — polynomial SAT construction and exact equivalence
-- statement:
--   For every CNF formula φ in the standing normalized domain of §3.3, the concrete instance Iφ is an assembling of basic blocks, can be constructed in time polynomial in the size of φ, and is 3DT-collapsible if and only if φ is satisfiable. The polynomial bound is uniform over all formulas. The domain has at least two clauses, at least two literal occurrences per clause, and at least two occurrences of each polarity of each appearing Boolean variable. The separate concrete normalization accepts all CNF formulas, including an empty conjunction and formulas containing an empty clause; the final NP-hardness goal has no normalization or satisfiability hypothesis.
--
--   Differences from the source:
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: a construction computable in polynomial time → one finite-alphabet one-tape Turing machine and exponent, uniform over every legal input, with bound size^k+k; reason: this is the published Cook machine model with actual step counting, not an output-length bound; compact syntax has polynomial length in the source size
--   - encoding: size of a formula over named variables → number of clauses plus literal occurrences, with names compactly renamed in its binary code; reason: only the pattern of repeated variable names matters; the code and its output have polynomial length in this size
--   - encoding: the chains and arbitrary order of the blocks in §3.3 → variable/positive-copy/negative-copy order, followed by clause, conjunction and feedback gates with fresh integer ports; reason: the source explicitly permits any block order; repeated literals retain distinct occurrence ports
--   - reading: the final conjunction input printed Γ_l on p.27 → the final clause variable Γ_γ; reason: p.29 explicitly identifies this same gate with Γ_γ; see insight I1
--   - reading: ellipses for two-leaf chains and the m−1 feedback gates → one gate for two leaves, and a direct formula wire when m=1; reason: these are the boundary cases of the stated chain construction, with no new restriction on formulas
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Theorem 19, printed p. 27 = PDF p. 27; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_SATConstruction

namespace BulteauTranspositions.NPHard

theorem theorem_19 :
    (∃ (Γ : Type) (_ : Fintype Γ) (ι : Bool ↪ Γ) (M : CookPvsNP.TM Γ) (k : ℕ),
      ∀ F : CookPvsNP.CNF, Normalized F →
        let time := (F.length + F.flatten.length) ^ k + k
        M.HaltsWithin time ((encodeFormula F).map ι) ∧
        M.output (M.run time (M.init ((encodeFormula F).map ι))) =
          (encodeInstance (satInstance F)).map (some ∘ ι)) ∧
    ∀ F : CookPvsNP.CNF, Normalized F →
      IsAssembly (assembly (satGates F)) ∧
      (F.Satisfiable ↔ Collapsible (satInstance F)) := by sorry

end BulteauTranspositions.NPHard
