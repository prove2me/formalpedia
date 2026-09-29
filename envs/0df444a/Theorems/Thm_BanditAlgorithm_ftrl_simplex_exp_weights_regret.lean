-- Prove2me | Theorems.Thm_BanditAlgorithm_ftrl_simplex_exp_weights_regret
-- name    : BanditAlgorithm.ftrl_simplex_exp_weights_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T17:02:03.494401+00:00
-- url     : https://prove2.me/theorems/98f48d26-8848-46db-b540-4541cb1581f6
-- statement:
--   (Regret on the simplex, Proposition 28.7) Let $\mathcal{A} = \mathcal{P}_{d-1}$ be the probability simplex and $y_t \in [0,1]^d$ for all $t$. FTRL (= mirror descent = exponential weights here, Example 28.3/Eq. (28.5); the book states the proposition for mirror descent and notes the identical FTRL bound via Theorem 28.5) with the unnormalised negentropy potential
--
--   $$F(a) = \sum_i (a_i \log a_i - a_i)$$
--
--   on domain $[0,\infty)^d$ and learning rate $\eta = \sqrt{2\log(d)/n}$ satisfies
--
--   $$R_n(a_0) \le \sqrt{2 n \log d}$$
--
--   for every simplex comparator $a_0$.
-- source:
--   L&S Proposition 28.7, p.335

import Definitions.Def_OnlineLinearOptimization


open RealInnerProductSpace

theorem BanditAlgorithm.ftrl_simplex_exp_weights_regret
    (d n : ℕ) (y a : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1)
    (hiter : IsFTRLIterates (Real.sqrt (2 * Real.log d / n))
      (fun v : EuclideanSpace ℝ (Fin d) => ∑ i, (v i * Real.log (v i) - v i))
      {v : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ v i}
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
      y a) :
    ∀ a₀ ∈ {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1},
      oloRegret a y n a₀ ≤ Real.sqrt (2 * n * Real.log d) := by
  sorry
