-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_lemma_7_4
-- name    : AutoregressiveCompression.Main.Supplement.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:14:08.65625+00:00
-- url     : https://prove2.me/theorems/db975a5c-4060-4b9f-a108-5e570d26a2b0
-- title:
--   Lemma 7.4 — Generator learning for circuit-samplable laws excludes auxiliary-input one-way functions
-- statement:
--   For a fixed finite alphabet $\Sigma$ with at least two symbols, let $\mathcal C^{\rm circ}_n$ consist of the uniform-seed laws of sampler circuits with at most $n$ gates and at most $n$ output symbols. Then
--
--   $$\mathcal C^{\rm circ}\text{ admits polynomial-time learning with generators}\ \Longrightarrow\ \text{auxiliary-input one-way functions do not exist}.$$
--
--   One learner must work on every size slice and every circuit-induced law. Nonexistence uses the strict all-auxiliary-input inversion definition of Definition 7.2. This support removes the cryptographic intermediate condition in Theorem 7.1.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
--   - encoding: auxiliary-input families and strict all-x inversion with reciprocal-polynomial error → finite uniform programs with exact natural-valued polynomial length functions, independent finite seed and inverter coins, a positive natural-coefficient polynomial denominator at every n, and strict greater-than success; reason: Definition 7.2 made operational; rational-polynomial certificates permit all natural-valued length polynomials, including negative coefficients; natural-coefficient upper bounds are cofinal for the existential hardness denominator, and larger denominators only strengthen the inversion requirement; malformed preimages fail and zero denominators are excluded as undefined tolerances
--   - encoding: sampler circuit size is number of gates, with output length at most n → the published fan-in-two Boolean vector circuits with gate-list size, uncharged input and output wires, and fixed one-hot symbol encoding; reason: the source fixes no gate basis; this commits to an ordinary concrete basis and does not assume a comparison or reindexing theorem
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Lemma 7.4, printed p.38 / PDF p.40

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning
import Definitions.Def_AutoregressiveCompression_Main_Supplement_CircuitClass
import Definitions.Def_AutoregressiveCompression_Main_Supplement_AuxiliaryInput

namespace AutoregressiveCompression.Main.Supplement

/-- Lemma 7.4, printed p.38 / PDF p.40. The conclusion is the negation
of the source's auxiliary-input existence predicate, with its strict threshold. -/
theorem lemma_7_4 {Sym : Type} [Fintype Sym] [Nontrivial Sym]
    (h : GeneratorLearnable (Ccirc Sym)) :
    ¬ AuxiliaryOneWayFunctionsExist := by sorry

end AutoregressiveCompression.Main.Supplement
