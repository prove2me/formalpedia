-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_finite_reward_le_index_policy_add_terminal
-- name    : BanditAlgorithm.gittins_finite_reward_le_index_policy_add_terminal
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T15:54:00.236704+00:00
-- url     : https://prove2.me/theorems/7e72b151-9907-4d25-8d52-0dcaf4ea1565
-- title:
--   Finite prevailing-charge bound with terminal retirement potential
-- statement:
--   Consider a $k$-armed rested Markov bandit with measurable rewards, discount factor $0<\alpha<1$, and integrable discounted absolute rewards.  Let $\pi^*$ be a policy that always selects an arm of maximal current Gittins index.  For every competing policy $\pi$, initial state vector $x$, and horizon $N$,
--
--   $$
--   \sum_{n<N}\alpha^n\,\mathbb E_\pi[r_n]
--   \le
--   \sum_{n<N}\alpha^n\,\mathbb E_{\pi^*}[r_n]
--   +\alpha^N U_N^{\pi^*},
--   $$
--
--   where $U_N^{\pi^*}$ is the expected terminal retirement potential evaluated at the prevailing charges after $N$ rounds.
--
--   This is the finite-horizon accounting form of the prevailing-charge proof.  It isolates the pathwise greedy interleaving comparison from the subsequent infinite-horizon tail passage.
--
--   **Formalization Note** The two finite discounted sums use the platform's round-reward marginals, while the final term uses `markovBanditExpectedRetirementPotential`.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, §35.4, proof of Theorem 35.9, Parts 1–2, printed pp. 451–453 / PDF pp. 459–461; finite greedy comparison is Lemma 35.10.

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_finite_reward_le_index_policy_add_terminal
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π πstar : MarkovBanditPolicy k S)
    (hπstar : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      α ^ n * markovBanditRoundReward P r π x n) ≤
      (∑ n ∈ Finset.range N,
        α ^ n * markovBanditRoundReward P r πstar x n) +
      α ^ N * markovBanditExpectedRetirementPotential
        P r α πstar x N := by
  sorry
