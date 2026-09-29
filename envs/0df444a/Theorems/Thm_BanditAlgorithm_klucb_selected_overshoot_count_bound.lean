-- Prove2me | Theorems.Thm_BanditAlgorithm_klucb_selected_overshoot_count_bound
-- name    : BanditAlgorithm.klucb_selected_overshoot_count_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T02:27:26.367394+00:00
-- url     : https://prove2.me/theorems/fbf1cc45-de8c-478a-83b5-7cf23ca686f5
-- title:
--   KL-UCB selected-arm overshoot count bound
-- statement:
--   This is the selected-suboptimal-index count estimate used in the KL-UCB analysis.
--
--   Consider a finite Bernoulli bandit, fix an optimal arm $a$ and a suboptimal arm $i$, and choose $\varepsilon_1,\varepsilon_2>0$ with $\varepsilon_1+\varepsilon_2<\Delta_i$. Let $H_{a,i,\varepsilon_2}(n)$ count initialized rounds on which arm $i$ is selected and its KL-UCB index is at least $\mu^\star-\varepsilon_2$. Then
--
--   $$
--   \mathbb E_{\nu,\pi}[H_{a,i,\varepsilon_2}(n)]
--   \le
--   \frac{\log f(n)}
--   {d(\mu_i+\varepsilon_1,\,\mu^\star-\varepsilon_2)}
--   +\frac{1}{2\varepsilon_1^2},
--   $$
--
--   where $f(n)=1+n(\log n)^2$ and $d$ is the binary relative entropy.
--
--   This is the canonical-bandit selected-round form of Lemma 10.8 and supplies the information-theoretic term in the KL-UCB pull-count bound.
--
--   **Formalization Note** The expectation is an integral of the second KL-UCB failure count against the finite-history bandit measure. The optimal-arm witness is explicit to match the source proof.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, Lemma 10.8, printed pp. 138–139, instantiated in the proof of Theorem 10.6 on printed p. 139.

import Definitions.Def_klucbFailureCount

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.klucb_selected_overshoot_count_bound
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    {π : BanditAlgorithm.BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε₁ ε₂ : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hgap : 0 < BanditAlgorithm.banditGap ν i)
    (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂)
    (hεsum : ε₁ + ε₂ < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.klucbFailureCount ν a i ε₂ h).2) ≤
      Real.log (BanditAlgorithm.klucbExploration n) /
          BanditAlgorithm.bernoulliRelativeEntropy
            (BanditAlgorithm.banditArmMean ν i + ε₁)
            (BanditAlgorithm.banditOptimalMean ν - ε₂) +
        1 / (2 * ε₁ ^ 2) := by
  sorry
