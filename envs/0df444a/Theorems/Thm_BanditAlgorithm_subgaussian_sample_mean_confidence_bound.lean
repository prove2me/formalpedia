-- Prove2me | Theorems.Thm_BanditAlgorithm_subgaussian_sample_mean_confidence_bound
-- name    : BanditAlgorithm.subgaussian_sample_mean_confidence_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T18:20:26.877747+00:00
-- url     : https://prove2.me/theorems/98889c17-0d33-437b-8004-0da10798d303
-- statement:
--   (Confidence form — L&S Eqs. (5.6)-(5.7)) Under the same hypotheses, let $\delta \in (0,1)$. With probability at least $1-\delta$,
--
--   $$\mu < \hat\mu + \sqrt{\frac{2\sigma^2\log(1/\delta)}{n}},$$
--
--   stated as
--
--   $$\mathbb{P}\left(\hat\mu + \sqrt{\frac{2\sigma^2\log(1/\delta)}{n}} \le \mu\right) \le \delta.$$
--
--   This is the exact deviation bound the UCB index of Chapter 7 is built from.
-- source:
--   L&S Eqs. (5.6)-(5.7), p.78

import Mathlib.Probability.Moments.SubGaussian


open MeasureTheory ProbabilityTheory Real NNReal

theorem BanditAlgorithm.subgaussian_sample_mean_confidence_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {m : ℝ} {σ : ℝ≥0} (hσ : 0 < σ)
    (h_indep : iIndepFun (fun i ω ↦ X i ω - m) P)
    (h_subG : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - m) (σ ^ 2) P)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | (∑ i, X i ω) / n + Real.sqrt (2 * (σ : ℝ) ^ 2 * log (1 / δ) / n) ≤ m} ≤ δ := by
  sorry
