-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_theorem_1_3
-- name    : AgnosticImitate.Reduction.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:25:38.459122+00:00
-- url     : https://prove2.me/theorems/f124c258-2e0e-4a50-aac4-79e5db4870f3
-- title:
--   Theorem 1.3 — Algorithm 2 with a (C, γε)-conditional multiaccuracy oracle, f = sign_ε, γ = ε and T ≥ ε⁻² is a (C, O(ε))-agnostic learner; failure probability at most Tδ
-- statement:
--   There is a universal constant $K>0$ such that the following holds for every probability measure $\mu$ on $X$, admissible class $C$, label mean $g$, every $\varepsilon>0$ with $\varepsilon^{-1}\in\mathbb N$ and every horizon $T\ge\varepsilon^{-2}$. Run Algorithm 2 with soft threshold $f=\mathrm{sign}_\varepsilon$, grid size $\gamma=\varepsilon$ and a $(C,\gamma\varepsilon)$-conditional multiaccuracy oracle: in round $t$ the answer $r_t$ is any predictor that is $(C,\varepsilon^2)$-conditionally multiaccurate (per level set) with respect to $R_\gamma\circ\mathrm{sign}_\varepsilon\circ q_t$.
--
--   1. If every round is answered correctly, the output $p=\sum_{t=1}^Tt\,\mathrm{sign}_\varepsilon(q_t)/\binom{T+1}2$ satisfies
--   $$\mathbb E[|y-p(x)|]\le\inf_{c\in C}\mathbb E[|y-c(x)|]+K\varepsilon .$$
--   2. If each call fails with probability at most $\delta$, Algorithm 2 fails with probability at most $T\delta$.
--
--   Differences from the source:
--   - encoding: a labeled distribution D on X × {±1} with feature marginal D_X → a probability measure μ on a measurable space X and a measurable label mean g : X → [−1, 1] (IsPredictor g); E[φ(x, y)] = ∫ ((1+g)/2·φ(x, 1) + (1−g)/2·φ(x, −1)) dμ (expect); reason: every D with marginal D_X is determined by g(x) = E[y | x] up to μ-null sets, and all expectations agree
--   - encoding: predictors and class members p : X → [±1] → measurable real functions with values in [−1, 1] (IsPredictor); reason: the paper's expectations presuppose measurability; boundedness is the stated range
--   - encoding: min_{c∈C} E[|y − c(x)|] → ⨅ over the subtype C (IsAgnosticLearner); reason: C is nonempty (1 ∈ C) and the values are ≥ 0, so the infimum is the minimum whenever it exists, and the statement is at least as strong
--   - reading: (C, γε)-conditional multiaccuracy (no displayed definition) → per level set: for every value v and c ∈ C, |E[1{R_γ(sign_ε(q_t(x))) = v} c(x)(y − r_t(x))]| ≤ γε (IsCondMultiaccurate); reason: footnote 5 (p. 11: '(C, γε)-conditional multiaccuracy, applied to splitting functions with 1/γ level sets') and Theorem 1.1's counts force the per-level reading
--   - reading: R_γ rounds to multiples of γ → nearest multiple, γ·round(v/γ) with ties up (roundGrid); reason: the paper does not say which rounding; nearest rounding gives at most 2/γ + 1 level sets on [−1, 1]
--   - encoding: a call to a conditional multiaccuracy oracle → the answer is any predictor satisfying the per-level guarantee for D (label mean g) and the splitting function computed from earlier answers; the guarantee is stated for every transcript whose answers all satisfy it; reason: quantifying over all valid transcripts is quantifying over every adaptive adversarial oracle
--   - encoding: the error O(ε) → K·ε with a universal constant K chosen before X, μ, C, g, ε and T; reason: an O(·) with a universal constant
--   - encoding: grid size γ with γ^{−1} ∈ ℕ and γ = ε → 0 < ε and ∃ n : ℕ, ε⁻¹ = n; γ = ε; reason: Algorithm 2 requires γ^{−1} ∈ ℕ and the theorem sets γ = ε
--   - generalization: time horizon T = O(1/ε²) → every T ≥ ε⁻²; reason: the proof's error O(1/(εT) + ε) is O(ε) for every such T; T = ⌈ε⁻²⌉ is the printed choice
--   - encoding: rounds t = 1, …, T → Lean rounds t = 0, …, T − 1 (answer of round t is r t); reason: index shift only
--   - encoding: the oracle has failure probability δ; the algorithm has failure probability at most F → independent seeds ω : Fin N → Ω under the product measure Measure.pi P; for each call and each fixed choice of the other seeds the fresh seeds on which the call is answered incorrectly have P-measure ≤ δ, and each call's failure set is measurable (CallFailureBound); the product measure of the seeds on which the guarantee fails is ≤ F (failureProb); reason: fresh randomness per call is the paper's model; the paper presupposes that failure is an event, so measurability adds no condition
--   - generalization: an oracle call fails with probability at most δ given its query → the k-th answer may depend on the seeds of all earlier calls as well as its own fresh seed (RandOracle), not only on the history; reason: this covers every oracle whose answer is a function of the history and a fresh seed, which is the paper's oracle
--   - generalization: failure probability parameter δ in the probability range → every real δ, with bounds interpreted through ENNReal.ofReal; reason: for δ ≥ 0 these are the stated bounds; for δ < 0 each call must fail on a null set and the conclusion has bound zero; bounds above one remain valid
--   - generalization: probability of the measurable failure event → the product outer measure of the failure set, without requiring that final set to be measurable; reason: the final failure set is contained in the finite union of measurable call-failure events; its outer measure has the same union bound and agrees with probability whenever it is an event
--   - encoding: the algorithm succeeds by returning a predictor with the stated error guarantee → success includes IsPredictor of the output as well as the error inequality; reason: the source requires output in [-1,1]; a malformed or nonmeasurable output must not count as success merely because a totalized integral satisfies an inequality
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Theorem 1.3, p. 6 (PDF 8); proof p. 18 (PDF 20)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Setting
import Definitions.Def_AgnosticImitate_Reduction_Oracle
import Definitions.Def_AgnosticImitate_Reduction_Algorithms

open MeasureTheory

universe u v

namespace AgnosticImitate.Reduction

/-- Theorem 1.3 (Agnostic Learning, p. 6, PDF 8), for every horizon `T ≥ ε⁻²`. There is a
universal constant `K` such that for every `ε` with `ε⁻¹ ∈ ℕ`, Algorithm 2 with soft threshold
`f = sign_ε`, grid size `γ = ε`, horizon `T ≥ ε⁻²` and a `(C, γε)`-conditional multiaccuracy
oracle outputs `p` with `E[|y - p(x)|] ≤ min_{c ∈ C} E[|y - c(x)|] + K ε`, whatever (adaptive,
adversarial) correct answers the oracle gives; if each call fails with probability at most `δ`,
Algorithm 2 fails with probability at most `T δ`. -/
theorem theorem_1_3 :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (C : Set (X → ℝ)), IsAdmissibleClass C → ∀ g : X → ℝ, IsPredictor g →
        ∀ ε : ℝ, 0 < ε → (∃ n : ℕ, ε⁻¹ = n) → ∀ T : ℕ, ε⁻¹ ^ 2 ≤ T →
          (∀ r : ℕ → X → ℝ, (∀ t < T, alg2CallValid μ C g ε (signSoft ε) (ε * ε) t r) →
            IsAgnosticLearner μ C g (alg2Output (signSoft ε) r T) (K * ε)) ∧
          (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ : ℝ)
              (ans : RandOracle Ω X),
            CallFailureBound T P δ (alg2CallValid μ C g ε (signSoft ε) (ε * ε)) ans →
            failureProb T P ans
                (fun r => IsAgnosticLearner μ C g (alg2Output (signSoft ε) r T) (K * ε))
              ≤ ENNReal.ofReal (T * δ)) := by sorry

end AgnosticImitate.Reduction
