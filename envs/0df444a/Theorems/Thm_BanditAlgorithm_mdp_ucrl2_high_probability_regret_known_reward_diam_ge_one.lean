-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one
-- name    : BanditAlgorithm.mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:59:39.555507+00:00
-- url     : https://prove2.me/theorems/04ec5846-f00b-402d-9f4c-ccd0ec1c678f
-- title:
--   UCRL2 high-probability regret bound with known rewards
-- statement:
--   There is a universal constant $C>0$ with the following property. Fix positive numbers of states $S$, actions $A$, and rounds $n$, a confidence level $\delta\in(0,1)$, and a known reward function $r:\mathcal S\times\mathcal A\to[0,1]$. There is a policy, depending on these known quantities but not on the transition matrix, such that for every communicating MDP $M$ with reward function $r$, diameter $D(M)\ge1$, and every initial state distribution,
--
--   $$
--   \mathbb P\!\left(
--   \widehat R_n\ge C D(M)S\sqrt{A n\log\!\left(\frac{nSA}{\delta}\right)}
--   \right)\le\delta.
--   $$
--
--   This is the high-probability UCRL2 guarantee in the knowledge model of Sections 38.4–38.5, where only the transition matrix is unknown. The diameter guard removes the one-state zero-diameter degeneracy while retaining every nontrivial communicating MDP.
--
--   **Formalization Note** The bad event is written with a non-strict lower bound so that its probability bound is equivalent to the source's strict upper regret guarantee.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 38.6, printed p. 523 / PDF p. 532; known-reward standing assumption in Sections 38.4--38.5, printed pp. 522--524.

import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
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
                    ENNReal.ofReal δ := by
  sorry
