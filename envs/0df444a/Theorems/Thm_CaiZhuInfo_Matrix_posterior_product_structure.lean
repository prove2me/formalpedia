-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_posterior_product_structure
-- name    : CaiZhuInfo.Matrix.posterior_product_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:32.432287+00:00
-- url     : https://prove2.me/theorems/21844110-9a31-4c16-a15f-63eeb9ab5c0f
-- title:
--   Lemma 6.1 — Posterior product structure
-- statement:
--   Let $X,Y$ be independent uniform inputs to a finite protocol with transcript $\Pi$. Their actual conditional law factors almost everywhere, and for each measurable transcript singleton of positive probability the atomic conditional law satisfies
--   $$P_{X,Y\mid\Pi=\pi}=P_{X\mid\pi}\times P_{Y\mid\pi}.$$
--   Moreover,
--   $$\mathrm{IC}_{U_X\times U_Y}(\Pi)=\mathbb E_\Pi\big[D(P_{X\mid\Pi}\|U_X)+D(P_{Y\mid\Pi}\|U_Y)\big].$$
--   Both the product identity and information-cost identity are conclusions derived from operational execution. These connect the scalar prediction results to information complexity.
--
--   Differences from the source:
--   - encoding: finite randomized protocols with public and private randomness → finite binary trees with independent measurable tape probability spaces and derived execution laws; reason: finite messages admit binary coding and arbitrary real mixture probabilities are retained; no common round bound is imposed
--   - encoding: positive-probability transcript conditional laws → conditional-expectation posteriors almost everywhere plus the displayed identity on every positive measurable transcript singleton; reason: arbitrary public randomness can be nonatomic; the atomic formula is retained wherever its conditioning event is defined
--   - encoding: information cost I(X;Π | Y) + I(Y;Π | X), with Π containing the public tape and every message → I(H;X | Y,R) + I(H;Y | X,R), where H is the finite complete-history label and R is the public tape; reason: independence of the public tape from the inputs, the chain rule and symmetry of conditional mutual information give the same cost; the finite first slot also covers infinite discrete input alphabets
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 6.1, printed p.19 / PDF p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem posterior_product_structure {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (P : Protocol X Y Z) :
    let μ := independentLaw (uniformLaw X) (uniformLaw Y)
    (∀ᵐ ω ∂(P.executionLaw μ), ∀ x y,
      P.posteriorXY μ x y ω = P.posteriorX μ x ω * P.posteriorY μ y ω) ∧
    (∀ π : P.Transcript, MeasurableSet {π} → (P.transcriptLaw μ) {π} ≠ 0 →
      ∀ x y, P.atomicPosterior μ π x y =
        (∑ y', P.atomicPosterior μ π x y') * (∑ x', P.atomicPosterior μ π x' y)) ∧
    P.informationCost μ = ∫ ω,
      (logTwo (Fintype.card X) - FuchsVdGraaf.entropy (fun x => P.posteriorX μ x ω)) +
      (logTwo (Fintype.card Y) - FuchsVdGraaf.entropy (fun y => P.posteriorY μ y ω))
      ∂(P.executionLaw μ) := by sorry

end CaiZhuInfo.Matrix
