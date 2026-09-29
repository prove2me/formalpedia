-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_regret_bound
-- name    : BanditAlgorithm.bandit_kl_ucb_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T01:50:30.12009+00:00
-- url     : https://prove2.me/theorems/fa786e79-d0b1-4e7e-9919-e8d6fcdd9cef
-- statement:
--   (KL-UCB regret bound, GOAL, L&S Theorem 10.6) If the reward in round $t$ is $X_t \sim \mathcal{B}(\mu_{A_t})$ — i.e. the environment is `bernoulliBandit` for a mean vector $\mu \in [0,1]^k$ — then the regret of Algorithm 8 (KL-UCB with $f(t) = 1+t\log^2 t$) satisfies, for every $n$,
--
--   $$R_n \le \sum_{i:\Delta_i>0} \Delta_i\left(\frac{\log f(n)}{d(\mu_i+\varepsilon_1^i,\ \mu^*-\varepsilon_2^i)} + \frac{1}{2(\varepsilon_1^i)^2} + \frac{2}{(\varepsilon_2^i)^2}\right)$$
--
--   for EVERY family $\varepsilon_1, \varepsilon_2$ with $\varepsilon_1^i, \varepsilon_2^i > 0$ and $\varepsilon_1^i + \varepsilon_2^i \in (0, \Delta_i)$ at each suboptimal arm ($\forall$-family encoding of the book's infimum), and furthermore
--
--   $$\limsup_{n\to\infty} \frac{R_n}{\log n} \le \sum_{i:\Delta_i>0} \frac{\Delta_i}{d(\mu_i, \mu^*)},$$
--
--   stated in $\overline{\mathbb{R}}_{\ge 0}$ (a zero/junk divergence contributes $\infty$), mirroring the liminf style of `bandit_instance_dependent_lower_bound`.
-- source:
--   L&S Theorem 10.6, p.137

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditRegret


open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_kl_ucb_regret_bound {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π) :
    (∀ n : ℕ, ∀ ε₁ ε₂ : Fin k → ℝ,
      (∀ i, 0 < banditGap ν i →
        0 < ε₁ i ∧ 0 < ε₂ i ∧ ε₁ i + ε₂ i < banditGap ν i) →
      banditRegret ν π n ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
          banditGap ν i *
            (Real.log (klucbExploration n) /
                bernoulliRelativeEntropy (banditArmMean ν i + ε₁ i)
                  (banditOptimalMean ν - ε₂ i) +
              1 / (2 * ε₁ i ^ 2) + 2 / ε₂ i ^ 2)) ∧
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        ENNReal.ofReal (banditGap ν i) /
          ENNReal.ofReal
            (bernoulliRelativeEntropy (banditArmMean ν i)
              (banditOptimalMean ν)) := by
  sorry
