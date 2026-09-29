-- Prove2me | Theorems.Thm_BanditAlgorithm_best_arm_identification_sequential_halving_clog
-- name    : BanditAlgorithm.best_arm_identification_sequential_halving_clog
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T18:19:56.339498+00:00
-- url     : https://prove2.me/theorems/0e3fae2a-abe3-47d5-9bdc-02a3d1096467
-- title:
--   Theorem 33.10: Sequential Halving with L phases
-- statement:
--   Let $L=\lceil\log_2 k\rceil$. For a sorted $k$-armed 1-subgaussian bandit, suppose $n\ge kL$ and $H_2$ bounds $(i+1)/\Delta_i^2$ for every suboptimal arm. Any policy and recommendation rule implementing Sequential Halving satisfies
--
--   $$\mathbb P(\Delta_{A_{n+1}}>0)\le 3L\exp\!\left(-\frac{n}{16H_2L}\right).$$
--
--   This uses the exact natural-number phase count in Algorithm 22 rather than the real-valued `logb` expression.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (2020), Theorem 33.10 p. 412 and Exercise 33.8 pp. 419-420; L is formalized as Nat.clog 2 k.

import Definitions.Def_SequentialHalving

open MeasureTheory

theorem BanditAlgorithm.best_arm_identification_sequential_halving_clog {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (rec : BanditHistory k n → Fin k)
    (hπ : IsSequentialHalvingPolicy k n π rec) :
    (banditMeasure ν π n).real {h | 0 < banditGap ν (rec h)} ≤
      3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  sorry
