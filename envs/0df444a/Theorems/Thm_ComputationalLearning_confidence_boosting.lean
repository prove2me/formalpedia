-- Prove2me | Theorems.Thm_ComputationalLearning_confidence_boosting
-- name    : ComputationalLearning.confidence_boosting
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:20:43.629994+00:00
-- url     : https://prove2.me/theorems/d1e1cbba-d54b-46bb-8d8f-06c04914523c
-- title:
--   Boosting the confidence (§4.2): k independent runs all fail with probability ≤ (1 − δ₀)^k, and selecting the fewest-mistakes hypothesis loses at most γ
-- statement:
--   **§4.2** (pp. 76–77). Simulate $L$ a total of $k$ times on independent samples; the probability that all of $h_1, \dots, h_k$ have error larger than $\epsilon$ is at most $(1 - \delta_0)^k$ (solving $(1-\delta_0)^k \le \delta/2$ yields $k \ge (1/\delta_0)\ln(2/\delta)$). Then draw a sample $S$ of $(c_0/\gamma^2)\log(2k/\delta)$ examples and output the $h_i$ that makes the fewest mistakes on $S$: by the Chernoff bounds each empirical error is within $\gamma/2$ of the true error with confidence $1 - \delta/2k$, and by the union bound the output has error at most $\epsilon + \gamma$ with confidence $1 - \delta/2$.
--
--   Formally: (i) for any learner $L$ on samples of size $m$ whose hypothesis has error greater than $\epsilon$ with probability at most $1 - \delta_0$, on $k$ independent samples all $k$ hypotheses have error greater than $\epsilon$ with probability at most $(1-\delta_0)^k$; (ii) for measurable $h_1, \dots, h_k$ one of which has error at most $\epsilon$, $\gamma > 0$, and any rule selecting on a sample of $m$ examples a hypothesis with the fewest mistakes, the selected hypothesis has error greater than $\epsilon + \gamma$ with probability at most $2k\,e^{-m\gamma^2/2}$ (the additive Chernoff bound at accuracy $\gamma/2$ and the union bound; the book's $c_0$ is $2$ with natural logarithms).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §4.2 pp. 76-77, the confidence boosting procedure and its analysis

import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **Boosting the confidence** (§4.2, pp. 76–77). (i) If a learner `L` on samples of size `m` finds
a hypothesis of error at most `ε` with probability at least `δ₀` (for the target `c` and
distribution `D`), then on `k` independent samples all `k` hypotheses have error greater than
`ε` with probability at most `(1 − δ₀)^k` (at most `δ/2` for `k ≥ (1/δ₀) ln(2/δ)`). (ii) Given
hypotheses `h₁, …, h_k` at least one of which has error at most `ε`, choosing on a fresh sample
of `m` examples a hypothesis with the fewest mistakes yields, with probability at least
`1 − 2k e^{−mγ²/2}` (the Chernoff bound with accuracy `γ/2` for each of the `k` hypotheses and
the union bound), a hypothesis of error at most `ε + γ`; the book's `(c₀/γ²) log(2k/δ)` examples
are `m ≥ (2/γ²) ln(4k/δ)` with this constant. -/
theorem confidence_boosting {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} :
    (∀ (m : ℕ) (L : (Fin m → X × Bool) → X → Bool) {δ₀ : ℝ}, 0 ≤ δ₀ → δ₀ ≤ 1 →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀) →
      ∀ k : ℕ, blockSampleLaw D c k m {B | ∀ i, ε < errorOf D c (L (B i))} ≤
        ENNReal.ofReal ((1 - δ₀) ^ k)) ∧
    (∀ (k : ℕ) (h : Fin k → X → Bool), (∀ i, Measurable (h i)) → (∃ i, errorOf D c (h i) ≤ ε) →
      ∀ {γ : ℝ}, 0 < γ → ∀ (m : ℕ) (sel : (Fin m → X × Bool) → Fin k),
        (∀ S j, mistakes (h (sel S)) S ≤ mistakes (h j) S) →
        sampleLaw D c m {S | ε + γ < errorOf D c (h (sel S))} ≤
          ENNReal.ofReal (2 * k * Real.exp (-(m * γ ^ 2 / 2)))) := by sorry

end ComputationalLearning
