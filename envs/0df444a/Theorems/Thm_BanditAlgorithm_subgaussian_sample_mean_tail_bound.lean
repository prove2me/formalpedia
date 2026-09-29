-- Prove2me | Theorems.Thm_BanditAlgorithm_subgaussian_sample_mean_tail_bound
-- name    : BanditAlgorithm.subgaussian_sample_mean_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T18:20:18.384949+00:00
-- url     : https://prove2.me/theorems/8f9069cc-91ae-4939-aa67-ac711053df10
-- statement:
--   (Hoeffding-type bound, GOAL — L&S Corollary 5.5) Assume $X_i - \mu$ are independent, $\sigma$-subgaussian random variables for $i = 1, \dots, n$ (with $\sigma > 0$), and let
--
--   $$\hat\mu = \frac{1}{n}\sum_{t=1}^n X_t$$
--
--   be the sample mean. Then for any $\varepsilon \ge 0$,
--
--   $$\mathbb{P}(\hat\mu \ge \mu + \varepsilon) \le \exp\!\left(-\frac{n\varepsilon^2}{2\sigma^2}\right) \quad\text{and}\quad \mathbb{P}(\hat\mu \le \mu - \varepsilon) \le \exp\!\left(-\frac{n\varepsilon^2}{2\sigma^2}\right).$$
--
--   (Here $\sigma$-subgaussian means Mathlib's `HasSubgaussianMGF` with variance proxy $\sigma^2$.)
-- source:
--   L&S Corollary 5.5, p.78

import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Real NNReal

theorem BanditAlgorithm.subgaussian_sample_mean_tail_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {m : ℝ} {σ : ℝ≥0} (hσ : 0 < σ)
    (h_indep : iIndepFun (fun i ω ↦ X i ω - m) P)
    (h_subG : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - m) (σ ^ 2) P)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | m + ε ≤ (∑ i, X i ω) / n} ≤
        exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) ∧
    P.real {ω | (∑ i, X i ω) / n ≤ m - ε} ≤
        exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) := by
  sorry
