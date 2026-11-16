-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_proposition_5_15
-- name    : AutoregressiveCompression.Main.Supplement.proposition_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:11:40.245719+00:00
-- url     : https://prove2.me/theorems/c7243b42-6ab3-4374-a490-d4f2a04b95e3
-- title:
--   Proposition 5.15 — Autoregressive learning gives both evaluators and generators
-- statement:
--   Let $\mathcal D$ be any size-indexed distribution class over a fixed finite alphabet $\Sigma$ with at least two symbols. If $\mathcal D$ admits polynomial-time autoregressive distribution learning, then
--
--   $$\mathcal D\text{ admits polynomial-time learning with evaluators and with generators}.$$
--
--   Both conclusions hold for the same unrestricted class. Neither prefix closure nor a target-specific sampling circuit is assumed. The two output representations are those of Definition 4.5, with the full uniform sample-learning contract. This supplies both representation branches needed by the companion results.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Proposition 5.15, printed p.32 / PDF p.34

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning

namespace AutoregressiveCompression.Main.Supplement

/-- Proposition 5.15, printed p.32 / PDF p.34: both output representations,
for every class, without prefix closure or a target sampler. -/
theorem proposition_5_15 {Sym : Type} [Fintype Sym] [Nontrivial Sym] (𝒟 : DistributionClass Sym)
    (h : AutoregressiveLearnable 𝒟) :
    EvaluatorLearnable 𝒟 ∧ GeneratorLearnable 𝒟 := by sorry

end AutoregressiveCompression.Main.Supplement
