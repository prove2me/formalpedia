-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_lemma_7_9
-- name    : AutoregressiveCompression.Main.Supplement.lemma_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:16:28.307294+00:00
-- url     : https://prove2.me/theorems/0018c4cf-f1a3-4209-b11e-7dd42d40d400
-- title:
--   Lemma 7.9 — Generator learnability passes to the padded random-prefix class
-- statement:
--   Let $\mathcal D$ be any size-indexed class over a finite alphabet $\Sigma$ with at least two symbols. Write $\operatorname{Prefix}(\mathcal D)$ for the published padded uniformly random prefix class over $\Sigma\cup\{\bot\}$. Then
--
--   $$\mathcal D\text{ learnable with generators}\ \Longrightarrow\ \operatorname{Prefix}(\mathcal D)\text{ learnable with generators},$$
--
--   with both tasks in uniform polynomial time. The conclusion learner receives only samples of the padded-prefix law; sample access to $\mathcal D$ is not an added input. The empty-string branch uses the base point-mass convention. Finite-bit approximation error for random truncation is included in the requested learning tolerance. This support transfers generator learning to the class needed by the companion separation theorem.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Lemma 7.9, printed p.41 / PDF p.43

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning

namespace AutoregressiveCompression.Main.Supplement

/-- Lemma 7.9, printed p.41 / PDF p.43: the conclusion learner receives
only padded-prefix samples. Length zero uses the published point-mass semantics.
Finite fair-bit approximation is included in the requested accuracy budget. -/
theorem lemma_7_9 {Sym : Type} [Fintype Sym] [Nontrivial Sym] (𝒟 : DistributionClass Sym)
    (h : GeneratorLearnable 𝒟) :
    GeneratorLearnable 𝒟.prefix := by sorry

end AutoregressiveCompression.Main.Supplement
