-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
-- name    : BanditAlgorithm.bandit_divergence_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T18:21:44.518274+00:00
-- url     : https://prove2.me/theorems/92b82d0d-6ed1-4e86-b5af-2bcdf09e9732
-- statement:
--   (Divergence decomposition) Let $\nu = (P_1,\dots,P_k)$ and $\nu' = (P_1',\dots,P_k')$ be reward distributions of two $k$-armed bandits, $\pi$ a fixed policy, and $\mathbb{P}_\nu, \mathbb{P}_{\nu'}$ the measures induced on the canonical bandit model by the $n$-round interconnection. Then
--
--   $$D(\mathbb{P}_\nu, \mathbb{P}_{\nu'}) = \sum_{i=1}^k \mathbb{E}_\nu[T_i(n)]\, D(P_i, P_i').$$
-- source:
--   L&S Lemma 15.1, Eq. (15.1), p.198

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_BanditPolicy


open MeasureTheory ProbabilityTheory InformationTheory

theorem BanditAlgorithm.bandit_divergence_decomposition {k : ℕ} (ν ν' : StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditPolicy k) (n : ℕ) :
    klDiv (banditMeasure ν π n) (banditMeasure ν' π n) =
      ∑ i, ENNReal.ofReal (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) *
        klDiv (ν.P i) (ν'.P i) := by
  sorry
