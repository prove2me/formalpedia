-- Prove2me | Theorems.Thm_BanditAlgorithm_bernoulli_chernoff_tail_bound
-- name    : BanditAlgorithm.bernoulli_chernoff_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T01:50:10.458283+00:00
-- url     : https://prove2.me/theorems/2ff8615d-146b-4443-b809-1b0004bf38ed
-- statement:
--   (Chernoff's bound, L&S Lemma 10.3) Let $X_1, \dots, X_n$ ($n \ge 1$) be independent random variables, Bernoulli distributed with mean $\mu \in [0,1]$ (law equality $\mathrm{map}(X_i)P = \mu\delta_1 + (1-\mu)\delta_0$), and let $\hat\mu = \frac{1}{n}\sum_t X_t$. Then for $\varepsilon \in [0, 1-\mu]$,
--
--   $$\mathbb{P}(\hat\mu \ge \mu + \varepsilon) \le \exp\big(-n\, d(\mu+\varepsilon, \mu)\big) \quad\text{(Eq. 10.1)},$$
--
--   and for $\varepsilon \in [0, \mu]$,
--
--   $$\mathbb{P}(\hat\mu \le \mu - \varepsilon) \le \exp\big(-n\, d(\mu-\varepsilon, \mu)\big) \quad\text{(Eq. 10.2)}.$$
--
--   - Both $\varepsilon$-ranges are the book's closed intervals, and both conclusions are stated as one conjunction.
--   - At $\mu \in \{0,1\}$ the junk-valued exponent makes the bound weaker than the book's $\exp(-\infty) = 0$ but still true.
-- source:
--   L&S Lemma 10.3, p.135 (with Corollary 10.4, p.136)

import Definitions.Def_bernoulliRelativeEntropy


open MeasureTheory ProbabilityTheory Real

theorem BanditAlgorithm.bernoulli_chernoff_tail_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    (∀ ε ∈ Set.Icc (0 : ℝ) (1 - μ),
      P.real {ω | μ + ε ≤ (∑ t, X t ω) / n} ≤
        exp (-(n * bernoulliRelativeEntropy (μ + ε) μ))) ∧
    (∀ ε ∈ Set.Icc (0 : ℝ) μ,
      P.real {ω | (∑ t, X t ω) / n ≤ μ - ε} ≤
        exp (-(n * bernoulliRelativeEntropy (μ - ε) μ))) := by
  sorry
