-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_stopping_time_sample_complexity_of_settling
-- name    : BanditAlgorithm.chernoff_stopping_time_sample_complexity_of_settling
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T14:30:00.948185+00:00
-- url     : https://prove2.me/theorems/4732a59a-c7a8-49be-a60d-e0c09b3af61e
-- title:
--   Sample complexity of Chernoff's stopping rule from a settling allocation
-- statement:
--   If the empirical allocation and the empirical means settle to an optimal allocation $\alpha^*$ with an **integrable** settling time (Garivier--Kaufmann Proposition 13), then Chernoff's stopping rule with the threshold $\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta)$ satisfies
--   $$\mathbb E[\tau_\delta]<\infty\quad\text{for every }\delta\in(0,1),\qquad \limsup_{\delta\to0^+}\frac{\mathbb E[\tau_\delta]}{\log(1/\delta)}\le c^*(\nu).$$
--
--   This is the upper half of Lattimore--Szepesv\'ari Theorem 33.6 for a fixed sampling rule; combined with the matching lower bound, which holds for every sound rule, it gives the limit.
--
--   Theorem 14 supplies, for each $\varepsilon>0$, a $\delta$-free integrable time $W_\varepsilon$ with $\tau_\delta\le W_\varepsilon+\lceil(1+\varepsilon)c^*(\nu)\log(1/\delta)\rceil$ almost surely. The passage to the statement above is bookkeeping, and it is what fixes where the $\varepsilon$ of Theorem 14 must sit: an $\varepsilon$ multiplying $\log(1/\delta)$ survives the limit while an additive one does not, so $\mathbb E[W_\varepsilon]$ is divided away by $\log(1/\delta)\to\infty$ and only $(1+\varepsilon)c^*$ remains. Taking $\varepsilon_0=\varepsilon/(2(c^*+1))$ makes $(1+\varepsilon_0)c^*\le c^*+\varepsilon/2$, and the additive constant is swallowed by the remaining $\varepsilon/2$ once $\delta$ is small.
--
--   The single-arm case is included rather than excluded: with $k=1$ there is no alternative hypothesis, $Z_t$ is an infimum over the empty set and hence $+\infty$, so the rule stops at round $0$ and both clauses are trivial. This is why the statement needs no lower bound on the number of arms, matching the hypothesis $0<k$ under which Theorem 33.6 is stated.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Theorem 14; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 33.6 (upper half) and Lemma 33.7.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.chernoff_stopping_time_sample_complexity_of_settling
    {k : ℕ} [NeZero k]
    (pol : BanditAlgorithm.BanditPolicy k) (μvec : Fin k → ℝ) {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (α : Fin k → NNReal) (hαpos : ∀ i, 0 < α i)
    (hopt : BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
      (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α)
    (hsettle : ∀ ξ : ℝ, 0 < ξ →
          (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
            ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
              ∂(BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∫⁻ ω, (BanditAlgorithm.chernoffStoppingTime (k := k) δ ω : ℝ≥0∞)
          ∂BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol ≠ ⊤) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (∫⁻ ω, (BanditAlgorithm.chernoffStoppingTime (k := k) δ ω : ℝ≥0∞)
              ∂BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol).toReal / Real.log (1 / δ)
            ≤ (BanditAlgorithm.baiComplexity (BanditAlgorithm.gaussianBandit μvec)
                (Set.range (BanditAlgorithm.gaussianBandit (k := k)))).toReal + ε := by
  sorry
