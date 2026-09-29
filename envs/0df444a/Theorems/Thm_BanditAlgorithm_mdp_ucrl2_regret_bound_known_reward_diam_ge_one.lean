-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_regret_bound_known_reward_diam_ge_one
-- name    : BanditAlgorithm.mdp_ucrl2_regret_bound_known_reward_diam_ge_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T18:29:22.339518+00:00
-- url     : https://prove2.me/theorems/c8c334e6-1a33-4c6a-b209-7c4ac6b1a6da
-- title:
--   Theorem 38.6: UCRL2 regret $O(DS\sqrt{An\log(nSA/\delta)})$ (corrected root)
-- statement:
--   (UCRL2 regret bound, GOAL, Theorem 38.6 + Eq. (38.12); corrected root — supersedes the Disproved `BanditAlgorithm.mdp_ucrl2_regret_bound`.) **Knowledge model** (L&S pp. 522-523, standing assumption of §38.4-38.5: *"we assume that only the transition matrix is unknown while the reward function is given"*): the reward function $r : \mathcal S \times \mathcal A \to [0,1]$ is quantified **before** the policy, so the learner may depend on $r$ (UCRL2 uses it) but not on the transition function; its observed history of state-action pairs then determines every received reward.
--
--   Let $S, A, n$ be positive and $\delta \in (0,1)$. For every reward function $r$ there is a policy $\pi$ such that for every strongly connected MDP $M = (\mathcal S, \mathcal A, P, r)$ with $S$ states, $A$ actions, diameter $D(M) \ge 1$, and every initial state distribution, with probability at least $1-\delta$ the random regret $\hat R_n = n\rho^* - \sum_{t=1}^n r_{A_t}(S_t)$ satisfies
--
--   $$\hat R_n < C\, D(M)\, S \sqrt{A n \log\left(\frac{n S A}{\delta}\right)},$$
--
--   encoded as $\mathbb P\big(\hat R_n \ge C D(M) S \sqrt{A n \log(nSA/\delta)}\big) \le \delta$. Moreover (Eq. (38.12), the same algorithm run with $\delta = 1/n$), for every $r$ there is a policy with
--
--   $$\mathbb E[\hat R_n] \le 1 + C\, D(M)\, S \sqrt{2 A n \log n}.$$
--
--   Both claims share one universal constant $C > 0$.
--
--   **Nondegeneracy guard.** The hypothesis $D(M) \ge 1$ is automatically satisfied by every strongly connected MDP with at least two states (travelling between distinct states takes at least one step). It excludes the degenerate one-state case $D(M) = 0$, where the purely multiplicative bound is $0$ and even the book's literal statement fails — the accepted disproof of the previous root instantiates exactly that case. It also excludes the junk value $D(M) = 0$ that the real-valued diameter assigns to non-strongly-connected MDPs (book: $D(M) = \infty$).
--
--   This is the capstone of Chapter 38: the price of learning an unknown transition structure under the average-reward criterion, complemented in this mission by the $\Omega(\sqrt{DSAn})$ lower bound (Theorem 38.7).
-- source:
--   L&S Theorem 38.6 + Eq. (38.12), pp.522-523 (knowledge model: p.522 "only the transition matrix is unknown while the reward function is given")

import Definitions.Def_FiniteMDPLearning
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_ucrl2_regret_bound_known_reward_diam_ge_one :
    ∃ C : ℝ, 0 < C ∧
      (∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
            ∃ π : MDPPolicy S A,
              ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
                1 ≤ mdpDiameter M →
                ∀ μ0 : MDPStateDistribution S,
                  mdpMeasure M μ0 π n
                      {h | C * mdpDiameter M * S *
                          Real.sqrt (A * n * Real.log (n * S * A / δ)) ≤
                        mdpRegret M n h} ≤
                    ENNReal.ofReal δ) ∧
      (∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
          ∃ π : MDPPolicy S A,
            ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
              1 ≤ mdpDiameter M →
              ∀ μ0 : MDPStateDistribution S,
                ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤
                  1 + C * mdpDiameter M * S *
                    Real.sqrt (2 * A * n * Real.log n)) := by
  sorry
