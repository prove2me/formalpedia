-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_minimax_gaussian_pair_regret_sum_lower_bound
-- name    : BanditAlgorithm.bandit_minimax_gaussian_pair_regret_sum_lower_bound
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-07-22T15:22:34.068535+00:00
-- url     : https://prove2.me/theorems/68ff6cd5-369b-4eea-bbdf-b4dda216d9d9
-- title:
--   Gaussian two-environment regret-sum lower bound
-- statement:
--   Let $k>1$, let $n\ge k-1$, and fix any policy $\pi$ for a $k$-armed bandit. There exist two mean vectors $\mu,\mu'\in[0,1]^k$ for unit-variance Gaussian bandits such that their regrets satisfy
--
--   $$
--   R_n(\pi,\nu_{\mu})+R_n(\pi,\nu_{\mu'})\;\ge\;\frac{2}{27}\sqrt{(k-1)n}.
--   $$
--
--   This is the two-environment testing certificate in the proof of the minimax lower bound. It is stronger than the final one-environment conclusion and is reusable in other Le Cam/Bretagnolle--Huber lower-bound arguments.
--
--   **Formalization Note** The two mean vectors are returned existentially together with their coordinatewise membership in $[0,1]$; the theorem is uniform over the policy.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), Theorem 15.2, printed pp. 199--201 / PDF pp. 208--210. The two-environment construction is on printed p. 200; Eq. (15.3), the Lemma 15.1 Gaussian-divergence bound, tuned gap, and final two-environment maximum argument are on printed p. 201.

import Definitions.Def_banditRegret
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_minimax_gaussian_pair_regret_sum_lower_bound
    {k n : ℕ} (hk : 1 < k) (hn : k - 1 ≤ n) (π : BanditPolicy k) :
    ∃ μ μ' : Fin k → ℝ,
      (∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, μ' i ∈ Set.Icc (0 : ℝ) 1) ∧
      2 * (Real.sqrt (((k : ℝ) - 1) * n) / 27) ≤
        banditRegret (gaussianBandit μ) π n +
          banditRegret (gaussianBandit μ') π n := by
  sorry
