-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_stopping_time_le_integrable_plus_linear_of_settling_time
-- name    : BanditAlgorithm.chernoff_stopping_time_le_integrable_plus_linear_of_settling_time
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:21:04.566222+00:00
-- url     : https://prove2.me/theorems/14b237fe-bb1c-4e78-af28-356b65170496
-- title:
--   Chernoff's stopping time $\le$ integrable time $+$ linear in $\log\tfrac1\delta$
-- statement:
--   Fix a Gaussian bandit $\nu=\mathcal N(\mu_1,1)\otimes\dots\otimes\mathcal N(\mu_k,1)$ with a unique best arm $i^*$ and at least two arms, and an optimal allocation $\alpha$ (a maximiser in Eq. (33.4)) with all weights strictly positive. Write
--   $$T_\xi(\omega)=\inf\{N\ge1:\ \text{for all }n\ge N,\ |T_i(n)/n-\alpha_i|\le\xi\text{ and }|\hat\mu_i(n)-\mu_i|\le\xi\text{ for every }i\}$$
--   for the round from which the empirical allocation and the empirical means have settled to within $\xi$. Assume that for every $\xi>0$ the sampling rule settles almost surely and $\mathbb E[T_\xi]<\infty$ — this is exactly the conclusion of Garivier & Kaufmann's Proposition 13. Then for every $\varepsilon>0$ there is a random time $W$, not depending on $\delta$, with $\mathbb E[W]<\infty$ and
--   $$\tau_\delta\ \le\ W+\left\lceil(1+\varepsilon)\,c^*(\nu)\,\log\tfrac1\delta\right\rceil\qquad\text{almost surely, for every }\delta\in(0,1).$$
--
--   Three multiplicative losses are incurred and no more, each of size $1+\theta$ with $\theta=\min(1,\varepsilon/7)$, so that $(1+\theta)^3\le1+7\theta\le1+\varepsilon$. First, the slope of the line the statistic must exceed is taken at $1/((1+\theta)c^*)$ rather than $1/c^*$, because the settling window $\xi$ has to be strictly positive and the pair rates degrade continuously in $\xi$. Second, the threshold constant obeys $f^{-1}(\delta)\le(1+\theta)\log(1/\delta)+C(k,\theta)$. Third, the crossing round is $(1+\theta)\beta_0/r$ rather than $\beta_0/r$, the extra $\theta$-share of the line paying for the logarithmic term $k\log(t^2+t)$. Every remaining cost is additive and free of $\delta$, hence joins $W$.
--
--   The integrability hypothesis is not removable and not implied by almost-sure tracking. Chernoff's rule cannot fire while some arm is unplayed, so a bound of the stated shape forces the expected time to play every arm to be finite; a rule that postpones the first pull of arm $2$ to a round $M$ with $M<\infty$ almost surely but $\mathbb E[M]=\infty$ still has $T_i(t)/t\to\alpha_i$ almost surely, and for it the conclusion fails. The quantitative input --- here $\mathbb E[T_\xi]<\infty$, in Garivier & Kaufmann the forced exploration of D-Tracking --- is doing real work.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016 (arXiv:1602.04589), Theorem 14, conditionally on their Proposition 13; upper half of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 33.6, p. 410.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Real NNReal ENNReal Filter Topology

theorem BanditAlgorithm.chernoff_stopping_time_le_integrable_plus_linear_of_settling_time
    {k : ℕ} [NeZero k] (pol : BanditAlgorithm.BanditPolicy k) (μvec : Fin k → ℝ)
    {istar : Fin k} (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hk2 : ∃ j : Fin k, j ≠ istar)
    (α : Fin k → NNReal) (hαpos : ∀ i, 0 < α i)
    (hopt : BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
      (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α)
    (hsettle : ∀ ξ : ℝ, 0 < ξ →
      (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol),
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
        ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
            (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
          ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : (ℕ → Fin k × ℝ) → ℕ,
      (∫⁻ ω, (W ω : ℝ≥0∞)
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤) ∧
        ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
          ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
            BanditAlgorithm.chernoffStoppingTime (k := k) δ ω
              ≤ ((W ω : ℕ∞) + ((⌈(1 + ε)
                  * (BanditAlgorithm.baiComplexity (BanditAlgorithm.gaussianBandit μvec)
                      (Set.range (BanditAlgorithm.gaussianBandit (k := k)))).toReal
                  * Real.log (1 / δ)⌉₊ : ℕ) : ℕ∞)) := by
  sorry
