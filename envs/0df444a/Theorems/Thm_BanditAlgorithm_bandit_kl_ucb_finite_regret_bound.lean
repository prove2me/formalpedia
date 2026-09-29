-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_finite_regret_bound
-- name    : BanditAlgorithm.bandit_kl_ucb_finite_regret_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T01:58:22.635717+00:00
-- url     : https://prove2.me/theorems/a07924b2-75c6-4c54-8fb8-70e9f4f0288e
-- title:
--   Finite-horizon regret bound for KL-UCB
-- statement:
--   This is the finite-horizon regret guarantee for KL-UCB on a Bernoulli bandit.
--
--   Consider a stochastic bandit with finitely many Bernoulli arms. Arm $i$ has mean $\mu_i\in[0,1]$; write $\mu^\star=\max_i\mu_i$, $\Delta_i=\mu^\star-\mu_i$, and
--   $$
--   d(p,q)=p\log\frac{p}{q}+(1-p)\log\frac{1-p}{1-q}
--   $$
--   for the binary relative entropy. Let $\pi$ be any policy satisfying the KL-UCB selection rule with exploration function $f(n)=1+n(\log n)^2$. For every horizon $n$ and every pair of arm-dependent tolerances $\varepsilon_{1,i},\varepsilon_{2,i}>0$ satisfying $\varepsilon_{1,i}+\varepsilon_{2,i}<\Delta_i$ on each suboptimal arm,
--
--   $$
--   R_n(\pi,\nu)\le
--   \sum_{i:\Delta_i>0}\Delta_i\left[
--   \frac{\log f(n)}
--   {d(\mu_i+\varepsilon_{1,i},\,\mu^\star-\varepsilon_{2,i})}
--   +\frac{1}{2\varepsilon_{1,i}^2}
--   +\frac{2}{\varepsilon_{2,i}^2}
--   \right].
--   $$
--
--   This estimate is the non-asymptotic part of the KL-UCB analysis and isolates the contribution of every suboptimal arm, making it reusable in finite-time regret arguments.
--
--   **Formalization Note** The bandit $\nu$ is explicitly identified with the Bernoulli bandit determined by the supplied mean vector. The tolerances are represented as functions on the finite arm type, and the sum is restricted to arms with strictly positive gap.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, Theorem 10.6, printed pp. 137 and 139–140 (finite-horizon claim; Lemmas 10.7 and 10.8 on pp. 138–139).

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_kl_ucb_finite_regret_bound
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π) :
    ∀ n : ℕ, ∀ ε₁ ε₂ : Fin k → ℝ,
      (∀ i, 0 < banditGap ν i →
        0 < ε₁ i ∧ 0 < ε₂ i ∧ ε₁ i + ε₂ i < banditGap ν i) →
      banditRegret ν π n ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
          banditGap ν i *
            (Real.log (klucbExploration n) /
                bernoulliRelativeEntropy (banditArmMean ν i + ε₁ i)
                  (banditOptimalMean ν - ε₂ i) +
              1 / (2 * ε₁ i ^ 2) + 2 / ε₂ i ^ 2) := by
  sorry
