-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_lemma_10
-- name    : BayesOptStop.Scheme.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:17:16.667192+00:00
-- url     : https://prove2.me/theorems/ee400eb2-cffc-42d6-8ba3-34f61960d7cd
-- title:
--   Lemma 10 — two-sided multiplicative Chernoff bound
-- statement:
--   Let $Y_1,\dots,Y_n$ be independent random variables with values in $[0,1]$ and $\bar Y=\frac1n\sum_iY_i$. For every $\theta\in[0,1]$,
--   $$\Pr\big[|\bar Y-\mathbb E\bar Y|>\theta\,\mathbb E\bar Y\big]\le2\exp\!\big(-\theta^2n\,\mathbb E\bar Y/3\big).$$
--
--   Differences from the source:
--   - encoding: independent random variables taking values in [0,1] → measurable Y i : Ω → ℝ on a probability space, iIndepFun, Y i x ∈ [0,1] at every point; reason: Lean convention; the same instances
--   - generalization: n ≥ 1 implicit → n : ℕ unrestricted; at n = 0, Ȳ = 0 and the bound holds trivially; reason: the positive-sample-size statement is unchanged; the extra empty family has zero average and an empty deviation event
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Lemma 10, App. D.1, p. 51

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BayesOptStop.Scheme

/-- **Lemma 10** (multiplicative Chernoff bound; AmaniHamedani, Aouad, Işık, Kesselheim, Saberi
2026, held STOC 2027 submission, SHA-256 fecfa05a…c4241, App. D.1, p. 51): for independent
`Y_1, …, Y_n` with values in `[0,1]` and `Ȳ = (1/n) ∑ Y_i`, for every `θ ∈ [0,1]`,
`Pr[|Ȳ - E Ȳ| > θ E Ȳ] ≤ 2 exp(-θ² n E Ȳ / 3)`. -/
theorem lemma_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hrange : ∀ i x, Y i x ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    P.real {x | θ * (∫ y, (∑ i, Y i y) / n ∂P) <
        |(∑ i, Y i x) / n - ∫ y, (∑ i, Y i y) / n ∂P|} ≤
      2 * Real.exp (-(θ ^ 2 * n * ∫ y, (∑ i, Y i y) / n ∂P) / 3) := by sorry

end BayesOptStop.Scheme
