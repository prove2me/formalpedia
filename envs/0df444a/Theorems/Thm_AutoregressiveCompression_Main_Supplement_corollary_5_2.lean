-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_corollary_5_2
-- name    : AutoregressiveCompression.Main.Supplement.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:13:28.723107+00:00
-- url     : https://prove2.me/theorems/ab46fa2a-5efa-402c-8e1e-d7afdc775b6c
-- title:
--   Corollary 5.2 — Eight equivalent tasks for every prefix-closed class
-- statement:
--   Fix a finite alphabet $\Sigma$ with at least two symbols and any size-indexed prefix-closed class $\mathcal D$. The following eight polynomial-time tasks on $\mathcal D$ are all equivalent:
--
--   1. Autoregressive distribution learning.
--   2. Public-coin universal compression.
--   3. Deterministic universal compression.
--   4. Randomized universal compression, meaning Yao's effective entropy equals Shannon entropy.
--   5. Public-coin universal compression without an efficient decoder.
--   6. Entropy estimation.
--   7. Entropy gap testing.
--   8. Distribution learning with evaluators.
--
--   $$ (1)\Longleftrightarrow(2)\Longleftrightarrow(3)\Longleftrightarrow(4)\Longleftrightarrow(5)\Longleftrightarrow(6)\Longleftrightarrow(7)\Longleftrightarrow(8). $$
--
--   The tasks act on the class itself, rather than its padded-prefix image. All compression-rate and decoder clauses and arbitrary-law estimator soundness are retained in the published task predicates. This is a support for Theorem 7.1 and the prefix-closed separation clause of Theorem 7.3.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
--   - encoding: the following conditions are equivalent → List.TFAE of every listed condition in source order; reason: TFAE expresses all pairwise equivalences, retaining every clause
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Corollary 5.2, printed p.21–22 / PDF p.23–24

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning

namespace AutoregressiveCompression.Main.Supplement

/-- Corollary 5.2, printed pp.21–22 / PDF pp.23–24: all eight tasks,
including evaluator learning and the full randomized/Shannon-rate contract. -/
theorem corollary_5_2 {Sym : Type} [Fintype Sym] [Nontrivial Sym] (𝒟 : DistributionClass Sym)
    (hclosed : 𝒟.PrefixClosed) :
    List.TFAE [AutoregressiveLearnable 𝒟,
      PublicCoinCompressible 𝒟,
      DeterministicCompressible 𝒟,
      RandomizedCompressible 𝒟,
      PublicCoinCompressibleInefficientDecoder 𝒟,
      EntropyEstimable 𝒟,
      EntropyGapTestable 𝒟,
      EvaluatorLearnable 𝒟] := by sorry

end AutoregressiveCompression.Main.Supplement
