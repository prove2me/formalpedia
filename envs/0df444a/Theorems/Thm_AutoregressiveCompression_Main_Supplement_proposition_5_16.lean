-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_proposition_5_16
-- name    : AutoregressiveCompression.Main.Supplement.proposition_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:12:23.411606+00:00
-- url     : https://prove2.me/theorems/0d3e4127-530a-453f-bce2-6e7e5d2beeec
-- title:
--   Proposition 5.16 — Prefix-closed evaluator learning gives autoregressive learning
-- statement:
--   Let $\mathcal D$ be a size-indexed class over a fixed finite alphabet $\Sigma$ with at least two symbols. Suppose every truncation of every member of $\mathcal D_n$ remains in that same slice. Then
--
--   $$\mathcal D\text{ learnable with evaluators}\ \Longrightarrow\ \mathcal D\text{ autoregressively learnable},$$
--
--   where both learning tasks are in uniform polynomial time as in Definition 4.5. Prefix closure is the only extra class hypothesis. This supplies the evaluator-to-autoregressive branch of Corollary 5.2.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Proposition 5.16, printed p.32 / PDF p.34

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning

namespace AutoregressiveCompression.Main.Supplement

/-- Proposition 5.16, printed p.32 / PDF p.34; proof continues on PDF p.35.
All truncations must remain in the same size slice. -/
theorem proposition_5_16 {Sym : Type} [Fintype Sym] [Nontrivial Sym] (𝒟 : DistributionClass Sym)
    (hclosed : 𝒟.PrefixClosed) (h : EvaluatorLearnable 𝒟) :
    AutoregressiveLearnable 𝒟 := by sorry

end AutoregressiveCompression.Main.Supplement
