-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_theorem_7_3
-- name    : AutoregressiveCompression.Main.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:17:00.016519+00:00
-- url     : https://prove2.me/theorems/974a0ae7-5269-429a-b816-62e3dab8cd97
-- title:
--   Theorem 7.3 — Auxiliary-input one-way functions exist iff each of the three specified learning separations exists
-- statement:
--   Fix a finite alphabet $\Sigma$ with at least two symbols. The following four conditions are equivalent:
--
--   1. Auxiliary-input one-way functions of Definition 7.2 exist.
--   2. Some size-indexed distribution class over $\Sigma$ admits polynomial-time learning with generators but does not admit polynomial-time learning with evaluators.
--   3. Some size-indexed distribution class over $\Sigma$ admits polynomial-time learning with generators but does not admit polynomial-time autoregressive learning.
--   4. Some prefix-closed size-indexed class over $\Sigma$ admits polynomial-time learning with generators and admits none of the eight tasks in Corollary 5.2: autoregressive learning, public-coin compression, deterministic compression, randomized/Yao compression at Shannon rate, public-coin compression without an efficient decoder, entropy estimation, entropy gap testing, and evaluator learning.
--
--   $$ (1)\Longleftrightarrow(2)\Longleftrightarrow(3)\Longleftrightarrow(4). $$
--
--   Each existential quantifier ranges over arbitrary real-law distribution classes. The classes in (2) and (3) have no prefix-closure or circuit-samplability restriction; in (4) the same class fails all eight tasks. Auxiliary-input hardness retains the strict inversion threshold and one uniform inverter for every auxiliary string. This unconditional companion theorem characterizes exactly when generator learning separates from the other tasks.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
--   - encoding: auxiliary-input families and strict all-x inversion with reciprocal-polynomial error → finite uniform programs with exact natural-valued polynomial length functions, independent finite seed and inverter coins, a positive natural-coefficient polynomial denominator at every n, and strict greater-than success; reason: Definition 7.2 made operational; rational-polynomial certificates permit all natural-valued length polynomials, including negative coefficients; natural-coefficient upper bounds are cofinal for the existential hardness denominator, and larger denominators only strengthen the inversion requirement; malformed preimages fail and zero denominators are excluded as undefined tolerances
--   - encoding: the following conditions are equivalent → List.TFAE of every listed condition in source order; reason: TFAE expresses all pairwise equivalences, retaining every clause
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Theorem 7.3, printed p.37–38 / PDF p.39–40

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning
import Definitions.Def_AutoregressiveCompression_Main_Supplement_AuxiliaryInput

namespace AutoregressiveCompression.Main.Supplement

/-- Theorem 7.3, printed pp.37–38 / PDF pp.39–40. All four equivalent
clauses. The first two existential classes have no closure or samplability
restriction. In clause four the same class fails each of the eight tasks. -/
theorem theorem_7_3 {Sym : Type} [Fintype Sym] [Nontrivial Sym] :
    List.TFAE [AuxiliaryOneWayFunctionsExist,
      (∃ 𝒟 : DistributionClass Sym, GeneratorLearnable 𝒟 ∧ ¬ EvaluatorLearnable 𝒟),
      (∃ 𝒟 : DistributionClass Sym, GeneratorLearnable 𝒟 ∧ ¬ AutoregressiveLearnable 𝒟),
      (∃ 𝒟 : DistributionClass Sym, 𝒟.PrefixClosed ∧ GeneratorLearnable 𝒟 ∧
        ¬ AutoregressiveLearnable 𝒟 ∧
        ¬ PublicCoinCompressible 𝒟 ∧
        ¬ DeterministicCompressible 𝒟 ∧
        ¬ RandomizedCompressible 𝒟 ∧
        ¬ PublicCoinCompressibleInefficientDecoder 𝒟 ∧
        ¬ EntropyEstimable 𝒟 ∧
        ¬ EntropyGapTestable 𝒟 ∧
        ¬ EvaluatorLearnable 𝒟)] := by sorry

end AutoregressiveCompression.Main.Supplement
