-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_theorem_1_2
-- name    : AgnosticImitate.Reduction.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:25:37.267837+00:00
-- url     : https://prove2.me/theorems/6afacdb8-8c4e-44a4-9fdc-24c8582df4bd
-- title:
--   Theorem 1.2 — the Conditional Multiaccuracy Algorithm: error |V|(ε + 1/T), failure probability at most |V|Tδ
-- statement:
--   Let $\mu$, $C$, $g$ be as in Theorem 3.1, and let $f:X\to V$ be a splitting function with finitely many values, $|V|=M$, and measurable level sets. Let $\varepsilon\in\mathbb R$ and $T\ge1$. Run Algorithm 1 for $T$ rounds with a $(C,\varepsilon)$-multiaccuracy oracle on each level set ($m=\mathbf 1\{f=v\}$) and stitch the outputs, $p(x)=p^{(f(x))}(x)$.
--
--   1. If every one of the $|V|T$ calls is answered correctly, then $p:X\to[\pm1]$ is a predictor and
--   $$\mathbb E\Big[\max_{c\in C}\big|\mathbb E[c(x)(y-p(x))\mid f(x)]\big|\Big]=\sum_{v\in V}\max_{c\in C}\big|\mathbb E[\mathbf 1\{f(x)=v\}\,c(x)(y-p(x))]\big|\le|V|\Big(\varepsilon+\frac1T\Big).$$
--   2. If each call fails with probability at most $\delta$, the Conditional Multiaccuracy Algorithm fails with probability at most $|V|T\delta$.
--
--   Differences from the source:
--   - encoding: a labeled distribution D on X × {±1} with feature marginal D_X → a probability measure μ on a measurable space X and a measurable label mean g : X → [−1, 1] (IsPredictor g); E[φ(x, y)] = ∫ ((1+g)/2·φ(x, 1) + (1−g)/2·φ(x, −1)) dμ (expect); reason: every D with marginal D_X is determined by g(x) = E[y | x] up to μ-null sets, and all expectations agree
--   - encoding: predictors and class members p : X → [±1] → measurable real functions with values in [−1, 1] (IsPredictor); reason: the paper's expectations presuppose measurability; boundedness is the stated range
--   - encoding: f : X → V with V finite → f : X → Fin M (M = |V|) with measurable level sets; reason: every finite V is in bijection with Fin |V|; the level sets must be events for the conditional expectation to exist
--   - encoding: a call to a (C, ε)-multiaccuracy oracle fed labels z with E[z | x, y] = m(x)·y + (1 − m(x))·p'(x) → the answer is any predictor that is (C, ε)-multiaccurate for the labeled distribution with marginal μ and label mean m·g + (1 − m)·p' (queryMean); the guarantee is stated for every transcript whose answers all satisfy this (adaptive, adversarial oracle); reason: the oracle's guarantee is about that population distribution; quantifying over all valid transcripts is quantifying over every adaptive adversary, and the sampling of z is part of how the oracle is fed
--   - encoding: E[max_{c∈C} |E[c(x)(y − p(x)) | f(x)]|] → Σ_{v} ⨆_{c∈C} |E[1{f(x) = v} c(x)(y − p(x))]| (real supremum over the nonempty class C of values bounded by 2); reason: on a finite partition the two are equal (Pr[f = v] · |E[· | f = v]| = |E[1{f = v} ·]|, and null level sets contribute 0); max over C written as ⨆ of absolute values
--   - encoding: Algorithm 1 run on each level set, in no stated order → level after level: call v·T + t is round t of level v; reason: the runs on different level sets do not interact; the order only fixes the call indices
--   - generalization: T = O(1/ε), bound O(|V|ε), failure O(|V|δ/ε) → every T ≥ 1, bound |V|(ε + 1/T), failure |V|·T·δ; reason: the proof applies Theorem 3.1 on each level set; T = ⌈1/ε⌉ gives the printed O-bounds
--   - encoding: rounds t = 1, …, T → Lean rounds t = 0, …, T − 1 (answer of round t is r t); reason: index shift only
--   - encoding: the oracle has failure probability δ; the algorithm has failure probability at most F → independent seeds ω : Fin N → Ω under the product measure Measure.pi P; for each call and each fixed choice of the other seeds the fresh seeds on which the call is answered incorrectly have P-measure ≤ δ, and each call's failure set is measurable (CallFailureBound); the product measure of the seeds on which the guarantee fails is ≤ F (failureProb); reason: fresh randomness per call is the paper's model; the paper presupposes that failure is an event, so measurability adds no condition
--   - generalization: an oracle call fails with probability at most δ given its query → the k-th answer may depend on the seeds of all earlier calls as well as its own fresh seed (RandOracle), not only on the history; reason: this covers every oracle whose answer is a function of the history and a fresh seed, which is the paper's oracle
--   - generalization: failure probability parameter δ in the probability range → every real δ, with bounds interpreted through ENNReal.ofReal; reason: for δ ≥ 0 these are the stated bounds; for δ < 0 each call must fail on a null set and the conclusion has bound zero; bounds above one remain valid
--   - generalization: probability of the measurable failure event → the product outer measure of the failure set, without requiring that final set to be measurable; reason: the final failure set is contained in the finite union of measurable call-failure events; its outer measure has the same union bound and agrees with probability whenever it is an event
--   - generalization: positive accuracy ε → every real ε; reason: zero accuracy gives the exact-oracle case; negative accuracy admits no valid answer because C contains 1, so the deterministic implication is vacuous and any failure premise with δ < 1 is impossible
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Theorem 1.2, p. 6 (PDF 8); proof p. 17 (PDF 19)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Setting
import Definitions.Def_AgnosticImitate_Reduction_Oracle
import Definitions.Def_AgnosticImitate_Reduction_Algorithms

open MeasureTheory

universe u v

namespace AgnosticImitate.Reduction

/-- Theorem 1.2 (p. 6, PDF 8), with the explicit bounds of its proof (p. 17, PDF 19) for every
`T ≥ 1`. For a splitting function `f : X → V` with `|V| = M` level sets (encoded as `Fin M`),
running Algorithm 1 for `T` rounds with a `(C, ε)`-multiaccuracy oracle on each level set and
stitching yields a predictor `p : X → [±1]` with
`E[max_{c ∈ C} |E[c(x)(y - p(x)) | f(x)]|] = Σ_v max_{c ∈ C} |E[1{f(x) = v} c(x)(y - p(x))]|
≤ |V| (ε + 1/T)`; if each of the `|V| T` calls fails with probability at most `δ`, the
Conditional Multiaccuracy Algorithm fails with probability at most `|V| T δ`. -/
theorem theorem_1_2 {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (C : Set (X → ℝ)) (hC : IsAdmissibleClass C) (g : X → ℝ) (hg : IsPredictor g)
    (M : ℕ) (f : X → Fin M) (hf : ∀ v : Fin M, MeasurableSet (f ⁻¹' {v}))
    (ε : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∀ r : ℕ → X → ℝ, (∀ k < M * T, cmaCallValid μ C g f T ε k r) →
      IsPredictor (cmaStitch f r T) ∧
      ∑ v : Fin M, (⨆ c : C,
          |expect μ g (fun x y => levelInd f v x * (c : X → ℝ) x * (y - cmaStitch f r T x))|)
        ≤ M * (ε + 1 / T)) ∧
    (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ : ℝ)
        (ans : RandOracle Ω X),
      CallFailureBound (M * T) P δ (cmaCallValid μ C g f T ε) ans →
      failureProb (M * T) P ans (fun r => IsPredictor (cmaStitch f r T) ∧
          ∑ v : Fin M, (⨆ c : C,
            |expect μ g (fun x y => levelInd f v x * (c : X → ℝ) x * (y - cmaStitch f r T x))|)
            ≤ M * (ε + 1 / T))
        ≤ ENNReal.ofReal (M * T * δ)) := by sorry

end AgnosticImitate.Reduction
