-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_asymptotic_regret_bound
-- name    : BanditAlgorithm.bandit_kl_ucb_asymptotic_regret_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T02:03:54.408081+00:00
-- url     : https://prove2.me/theorems/c1d49510-240f-4e33-9d18-fe2a9d327e76
-- title:
--   Asymptotic regret bound for KL-UCB
-- statement:
--   This is the asymptotic regret guarantee for KL-UCB on a Bernoulli bandit.
--
--   Consider a stochastic bandit with finitely many Bernoulli arms. Arm $i$ has mean $\mu_i\in[0,1]$; write $\mu^\star=\max_i\mu_i$, $\Delta_i=\mu^\star-\mu_i$, and
--   $$
--   d(p,q)=p\log\frac{p}{q}+(1-p)\log\frac{1-p}{1-q}
--   $$
--   for the binary relative entropy. If $\pi$ satisfies the KL-UCB selection rule with exploration function $f(n)=1+n(\log n)^2$, then
--
--   $$
--   \limsup_{n\to\infty}\frac{R_n(\pi,\nu)}{\log n}
--   \le
--   \sum_{i:\Delta_i>0}\frac{\Delta_i}{d(\mu_i,\mu^\star)}.
--   $$
--
--   The bound gives the optimal problem-dependent logarithmic rate for KL-UCB and is the asymptotic conclusion of the standard finite-time analysis.
--
--   **Formalization Note** The formal statement takes the limsup in the extended nonnegative reals after applying the nonnegative-real embedding to normalized regret. The bandit $\nu$ is explicitly identified with the Bernoulli bandit determined by the supplied mean vector.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, Theorem 10.6, printed p. 137; asymptotic derivation assigned as Exercise 10.2 with hint on printed pp. 141–142.

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_kl_ucb_asymptotic_regret_bound
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π) :
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        ENNReal.ofReal (banditGap ν i) /
          ENNReal.ofReal
            (bernoulliRelativeEntropy (banditArmMean ν i)
              (banditOptimalMean ν)) := by
  sorry
