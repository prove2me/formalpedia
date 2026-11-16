-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_Supplement_proposition_7_6
-- name    : AutoregressiveCompression.Main.Supplement.proposition_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:14:44.927057+00:00
-- url     : https://prove2.me/theorems/e73e088c-de17-41c6-b086-10a95d2c6dd3
-- title:
--   Proposition 7.6 — Generator learning implies entropy estimation in the absence of auxiliary-input one-way functions
-- statement:
--   Let $\mathcal D$ be any size-indexed class of distributions over a finite alphabet $\Sigma$ with at least two symbols. Suppose $\mathcal D$ admits polynomial-time distribution learning with generators and auxiliary-input one-way functions do not exist. Then
--
--   $$\mathcal D\text{ admits polynomial-time entropy estimation}.$$
--
--   The conclusion is the full Definition 4.12 predicate: completeness holds on $\mathcal D$ and the one-sided lower-estimate soundness holds for every law of the relevant sample length, including laws outside the class. No samplability of these soundness laws is assumed. This supplies the entropy branch of both companion theorems.
--
--   Differences from the source:
--   - encoding: a fixed finite alphabet with at least two symbols and size-indexed string laws → Fintype and Nontrivial on Sym, with the published DistributionClass and PMF interfaces; reason: the standing convention of Section 4.2; arbitrary real target masses and the empty-string case are preserved
--   - encoding: uniform polynomial-time sample learners outputting evaluators or generators → finite Program execution and fixed polynomial bounds with explicit circuit descriptions, normalized evaluator masses, and evaluated uniform-seed generator masses; reason: Definition 4.5 made operational using the existing bit/sample interface; no task reductions are assumed and fair-bit approximation errors must fit the requested tolerance
--   - encoding: auxiliary-input families and strict all-x inversion with reciprocal-polynomial error → finite uniform programs with exact natural-valued polynomial length functions, independent finite seed and inverter coins, a positive natural-coefficient polynomial denominator at every n, and strict greater-than success; reason: Definition 7.2 made operational; rational-polynomial certificates permit all natural-valued length polynomials, including negative coefficients; natural-coefficient upper bounds are cofinal for the existential hardness denominator, and larger denominators only strengthen the inversion requirement; malformed preimages fail and zero denominators are excluded as undefined tolerances
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Proposition 7.6, printed p.39 / PDF p.41

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning
import Definitions.Def_AutoregressiveCompression_Main_Supplement_AuxiliaryInput

namespace AutoregressiveCompression.Main.Supplement

/-- Proposition 7.6, printed p.39 / PDF p.41. No samplability assumption
on the target class or on the arbitrary laws in entropy-estimator soundness. -/
theorem proposition_7_6 {Sym : Type} [Fintype Sym] [Nontrivial Sym] (𝒟 : DistributionClass Sym)
    (h : GeneratorLearnable 𝒟) (hno : ¬ AuxiliaryOneWayFunctionsExist) :
    EntropyEstimable 𝒟 := by sorry

end AutoregressiveCompression.Main.Supplement
