-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_theorem_3_1
-- name    : AgnosticImitate.Reduction.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:25:32.776584+00:00
-- url     : https://prove2.me/theorems/29e47af3-9750-4100-9aa5-99cdde090263
-- title:
--   Theorem 3.1 — Algorithm 1 gives multiaccuracy reweighted by m, with error ε + 1/T and failure probability at most Tδ
-- statement:
--   Let $\mu$ be a probability measure on $X$, $C$ an admissible class, $g:X\to[-1,1]$ a label mean and $m:X\to[0,1]$ a measurable reweighting measure. Let $\varepsilon\in\mathbb R$ and $T\ge1$.
--
--   1. If every round of Algorithm 1 is answered by a predictor $p_t$ that is $(C,\varepsilon)$-multiaccurate for the labeled distribution with label mean $m\,g+(1-m)\,p_{t-1}$ ($p_0=0$), then the output $p=\frac1T\sum_{t=1}^Tp_t$ is a measurable $[-1,1]$-valued predictor and satisfies
--   $$\max_{c\in C}\big|\mathbb E[m(x)\,c(x)\,(y-p(x))]\big|\le\varepsilon+\frac1T .$$
--   2. If each oracle call fails with probability at most $\delta$ (independent seeds), the probability that this guarantee fails is at most $T\delta$.
--
--   Differences from the source:
--   - encoding: a labeled distribution D on X × {±1} with feature marginal D_X → a probability measure μ on a measurable space X and a measurable label mean g : X → [−1, 1] (IsPredictor g); E[φ(x, y)] = ∫ ((1+g)/2·φ(x, 1) + (1−g)/2·φ(x, −1)) dμ (expect); reason: every D with marginal D_X is determined by g(x) = E[y | x] up to μ-null sets, and all expectations agree
--   - encoding: predictors and class members p : X → [±1] → measurable real functions with values in [−1, 1] (IsPredictor); reason: the paper's expectations presuppose measurability; boundedness is the stated range
--   - encoding: reweighting measure m : X → [0, 1] → measurable m with values in [0, 1]; reason: makes the reweighted expectations integrals of bounded measurable functions
--   - encoding: a call to a (C, ε)-multiaccuracy oracle fed labels z with E[z | x, y] = m(x)·y + (1 − m(x))·p'(x) → the answer is any predictor that is (C, ε)-multiaccurate for the labeled distribution with marginal μ and label mean m·g + (1 − m)·p' (queryMean); the guarantee is stated for every transcript whose answers all satisfy this (adaptive, adversarial oracle); reason: the oracle's guarantee is about that population distribution; quantifying over all valid transcripts is quantifying over every adaptive adversary, and the sampling of z is part of how the oracle is fed
--   - encoding: max_{c∈C} |E[…]| ≤ bound → ∀ c ∈ C, |E[…]| ≤ bound; reason: a supremum is at most a bound iff every member is; the maximum need not be attained
--   - generalization: T = O(1/ε) and the bound O(ε) → every T ≥ 1 and the explicit bound ε + 1/T; reason: the proof (p. 17) gives ε + 1/T for every T; T = ⌈1/ε⌉ gives at most 2ε, the printed claim
--   - encoding: rounds t = 1, …, T → Lean rounds t = 0, …, T − 1 (answer of round t is r t); reason: index shift only
--   - encoding: the oracle has failure probability δ; the algorithm has failure probability at most F → independent seeds ω : Fin N → Ω under the product measure Measure.pi P; for each call and each fixed choice of the other seeds the fresh seeds on which the call is answered incorrectly have P-measure ≤ δ, and each call's failure set is measurable (CallFailureBound); the product measure of the seeds on which the guarantee fails is ≤ F (failureProb); reason: fresh randomness per call is the paper's model; the paper presupposes that failure is an event, so measurability adds no condition
--   - generalization: an oracle call fails with probability at most δ given its query → the k-th answer may depend on the seeds of all earlier calls as well as its own fresh seed (RandOracle), not only on the history; reason: this covers every oracle whose answer is a function of the history and a fresh seed, which is the paper's oracle
--   - generalization: failure probability parameter δ in the probability range → every real δ, with bounds interpreted through ENNReal.ofReal; reason: for δ ≥ 0 these are the stated bounds; for δ < 0 each call must fail on a null set and the conclusion has bound zero; bounds above one remain valid
--   - generalization: probability of the measurable failure event → the product outer measure of the failure set, without requiring that final set to be measurable; reason: the final failure set is contained in the finite union of measurable call-failure events; its outer measure has the same union bound and agrees with probability whenever it is an event
--   - encoding: the algorithm succeeds by returning a predictor with the stated error guarantee → success includes IsPredictor of the output as well as the error inequality; reason: the source requires output in [-1,1]; a malformed or nonmeasurable output must not count as success merely because a totalized integral satisfies an inequality
--   - generalization: positive accuracy ε → every real ε; reason: zero accuracy gives the exact-oracle case; negative accuracy admits no valid answer because C contains 1, so the deterministic implication is vacuous and any failure premise with δ < 1 is impossible
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Theorem 3.1, p. 17 (PDF 19); bound ε + 1/T from its proof, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Setting
import Definitions.Def_AgnosticImitate_Reduction_Oracle
import Definitions.Def_AgnosticImitate_Reduction_Algorithms

open MeasureTheory

universe u v

namespace AgnosticImitate.Reduction

/-- Theorem 3.1 (p. 17, PDF 19), with the proof's explicit bound `ε + 1/T` for every `T ≥ 1`.
Algorithm 1 with reweighting measure `m : X → [0, 1]` and a `(C, ε)`-multiaccuracy oracle, run for
`T` rounds, outputs `p` with `|E[m(x) c(x)(y - p(x))]| ≤ ε + 1/T` for every `c ∈ C`, whatever
(adaptive, adversarial) correct answers the oracle gives; if each call fails with probability at
most `δ` (independent seeds), the guarantee fails with probability at most `T δ`. -/
theorem theorem_3_1 {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (C : Set (X → ℝ)) (hC : IsAdmissibleClass C) (g : X → ℝ) (hg : IsPredictor g)
    (m : X → ℝ) (hm : Measurable m) (hm01 : ∀ x, m x ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∀ r : ℕ → X → ℝ, (∀ t < T, alg1CallValid μ C g m ε t r) →
      IsPredictor (alg1Output r T) ∧
      ∀ c ∈ C, |expect μ g (fun x y => m x * c x * (y - alg1Output r T x))| ≤ ε + 1 / T) ∧
    (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ : ℝ)
        (ans : RandOracle Ω X),
      CallFailureBound T P δ (alg1CallValid μ C g m ε) ans →
      failureProb T P ans (fun r => IsPredictor (alg1Output r T) ∧ ∀ c ∈ C,
          |expect μ g (fun x y => m x * c x * (y - alg1Output r T x))| ≤ ε + 1 / T)
        ≤ ENNReal.ofReal (T * δ)) := by sorry

end AgnosticImitate.Reduction
