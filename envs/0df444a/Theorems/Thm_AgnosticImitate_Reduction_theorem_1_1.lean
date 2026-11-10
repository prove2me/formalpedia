-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_theorem_1_1
-- name    : AgnosticImitate.Reduction.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:24:43.903698+00:00
-- url     : https://prove2.me/theorems/4cf1b67b-fadb-4e8b-875e-d9cd515268e7
-- title:
--   Theorem 1.1 (first bullet) — (C, ε)-agnostic learning from O(1/ε⁵) calls to a (C, Ω(ε²))-multiaccuracy oracle, failure probability O(δ/ε⁵)
-- statement:
--   There are universal constants $K_1,K_2,K_3>0$ such that for every $0<\varepsilon\le1$ there is an oracle reduction $R$ with $N\le K_1/\varepsilon^5$ calls — a list of measurable maps fixed before the feature space $X$, the feature distribution $D_X=\mu$, the class $C$ and the labels, whose queries $(m_k,p'_k)$ and output are pointwise functions of the earlier oracle answers — such that for every probability measure $\mu$ on $X$, every admissible class $C$ (containing $1$, closed under negation and convex combinations) and every label mean $g$:
--
--   1. whenever every (adaptive, adversarial) answer $r_k$ is a predictor that is $(C,\varepsilon^2/K_2)$-multiaccurate for the labeled distribution with marginal $\mu$ and label mean $m_kg+(1-m_k)p'_k$, the output $p$ is a $(C,\varepsilon)$-agnostic learner:
--   $$\mathbb E[|y-p(x)|]\le\inf_{c\in C}\mathbb E[|y-c(x)|]+\varepsilon;$$
--   2. if each call fails with probability at most $\delta$ (independent seeds), the reduction fails with probability at most $K_3\delta/\varepsilon^5$.
--
--   The reduction accesses the data distribution only through its calls to the $(C,\varepsilon^2/K_2)$-multiaccuracy oracle for $D_X$. The second bullet of Theorem 1.1 (the converse, from [TTV09, HKRR18]) is not part of this item.
--
--   Differences from the source:
--   - encoding: a labeled distribution D on X × {±1} with feature marginal D_X → a probability measure μ on a measurable space X and a measurable label mean g : X → [−1, 1] (IsPredictor g); E[φ(x, y)] = ∫ ((1+g)/2·φ(x, 1) + (1−g)/2·φ(x, −1)) dμ (expect); reason: every D with marginal D_X is determined by g(x) = E[y | x] up to μ-null sets, and all expectations agree
--   - encoding: predictors and class members p : X → [±1] → measurable real functions with values in [−1, 1] (IsPredictor); reason: the paper's expectations presuppose measurability; boundedness is the stated range
--   - encoding: min_{c∈C} E[|y − c(x)|] → ⨅ over the subtype C (IsAgnosticLearner); reason: C is nonempty (1 ∈ C) and the values are ≥ 0, so the infimum is the minimum whenever it exists, and the statement is at least as strong
--   - generalization: a (C, ε)-agnostic learning algorithm that only accesses the data distribution via oracle calls → a pointwise oracle reduction (OracleReduction, IsAdmissible): queries and output are Borel functions of the earlier answers' values; reason: an algorithm of this form accesses the data only through the oracle, and the paper's reduction (Algorithms 1–2) is of this form, so asserting one exists is at least as strong
--   - generalization: for all feature distributions D_X and model classes C there exists an algorithm → the reduction is chosen before X, μ, C and g; reason: one reduction for all instances specializes to the paper's order of quantifiers
--   - encoding: a call to a (C, ε²/K₂)-multiaccuracy oracle fed labels z with E[z | x, y] = m(x)·y + (1 − m(x))·p'(x) → the answer is any predictor that is (C, ε²/K₂)-multiaccurate for the labeled distribution with marginal μ and label mean m·g + (1 − m)·p' (queryMean); the guarantee is stated for every transcript whose answers all satisfy this (adaptive, adversarial oracle); reason: the oracle's guarantee is about that population distribution; quantifying over all valid transcripts is quantifying over every adaptive adversary, and the sampling of z is part of how the oracle is fed
--   - encoding: O(1/ε⁵) calls, a (C, Ω(ε²))-multiaccuracy oracle, failure probability O(δ/ε⁵) (§1.4.3) → N ≤ K₁/ε⁵, accuracy ε²/K₂, failure ≤ K₃δ/ε⁵ with universal constants K₁, K₂, K₃ > 0 chosen before ε; reason: an O(·)/Ω(·) with universal constants, uniform in ε and the instance
--   - reading: 'statistically and computationally equivalent' and 'for all ε' → the call count and oracle accuracy above for every 0 < ε ≤ 1; reason: the theorem defines the equivalence by its bullets ('in the sense that'); no running-time model is stated
--   - encoding: the oracle has failure probability δ; the algorithm has failure probability at most F → independent seeds ω : Fin N → Ω under the product measure Measure.pi P; for each call and each fixed choice of the other seeds the fresh seeds on which the call is answered incorrectly have P-measure ≤ δ, and each call's failure set is measurable (CallFailureBound); the product measure of the seeds on which the guarantee fails is ≤ F (failureProb); reason: fresh randomness per call is the paper's model; the paper presupposes that failure is an event, so measurability adds no condition
--   - generalization: an oracle call fails with probability at most δ given its query → the k-th answer may depend on the seeds of all earlier calls as well as its own fresh seed (RandOracle), not only on the history; reason: this covers every oracle whose answer is a function of the history and a fresh seed, which is the paper's oracle
--   - generalization: failure probability parameter δ in the probability range → every real δ, with bounds interpreted through ENNReal.ofReal; reason: for δ ≥ 0 these are the stated bounds; for δ < 0 each call must fail on a null set and the conclusion has bound zero; bounds above one remain valid
--   - generalization: probability of the measurable failure event → the product outer measure of the failure set, without requiring that final set to be measurable; reason: the final failure set is contained in the finite union of measurable call-failure events; its outer measure has the same union bound and agrees with probability whenever it is an event
--   - encoding: the algorithm succeeds by returning a predictor with the stated error guarantee → success includes IsPredictor of the output as well as the error inequality; reason: the source requires output in [-1,1]; a malformed or nonmeasurable output must not count as success merely because a totalized integral satisfies an inequality
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Theorem 1.1 (first bullet), p. 2 (PDF 4); composition §1.3 and §1.4.3 (pp. 5–6, 12; PDF 7–8, 14)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Setting
import Definitions.Def_AgnosticImitate_Reduction_Oracle

open MeasureTheory

universe u v

namespace AgnosticImitate.Reduction

/-- Theorem 1.1 (Main), first bullet (p. 2, PDF 4). There are universal constants `K₁, K₂, K₃ > 0`
such that for every `0 < ε ≤ 1` there is an oracle reduction with at most `K₁/ε⁵` calls, fixed
before the feature space `X`, the feature distribution `D_X = μ`, the class `C` and the labels,
which accesses the data only through its calls to a `(C, ε²/K₂)`-multiaccuracy oracle for
`D_X` and is a `(C, ε)`-agnostic learner: whenever every (adaptive, adversarial) answer is
`(C, ε²/K₂)`-multiaccurate for its query, the output `p` satisfies
`E[|y - p(x)|] ≤ inf_{c ∈ C} E[|y - c(x)|] + ε`; and if each call fails with probability at most
`δ` (independent seeds), the reduction fails with probability at most `K₃ δ / ε⁵`. -/
theorem theorem_1_1 :
    ∃ K₁ K₂ K₃ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ 0 < K₃ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (N : ℕ) (R : OracleReduction N), R.IsAdmissible ∧ (N : ℝ) ≤ K₁ / ε ^ 5 ∧
          ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
            (C : Set (X → ℝ)), IsAdmissibleClass C → ∀ g : X → ℝ, IsPredictor g →
            (∀ r : ℕ → X → ℝ, (∀ k < N, R.CallValid μ C g (ε ^ 2 / K₂) k r) →
              IsAgnosticLearner μ C g (R.output r) ε) ∧
            (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
                (δ : ℝ) (ans : RandOracle Ω X),
              CallFailureBound N P δ (R.CallValid μ C g (ε ^ 2 / K₂)) ans →
              failureProb N P ans (fun r => IsAgnosticLearner μ C g (R.output r) ε)
                ≤ ENNReal.ofReal (K₃ * δ / ε ^ 5)) := by sorry

end AgnosticImitate.Reduction
