-- Prove2me | Theorems.Thm_BanditAlgorithm_best_arm_identification_sequential_halving
-- name    : BanditAlgorithm.best_arm_identification_sequential_halving
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-07-30T03:29:11.55482+00:00
-- url     : https://prove2.me/theorems/65add977-cf84-4b83-ace8-bd83e06f955b
-- statement:
--   (Fixed budget: sequential halving, Theorem 33.10) Let $\nu\in\mathcal{E}^k_{SG}(1)$ be a 1-subgaussian bandit with means sorted decreasingly ($\mu_1\ge\dots\ge\mu_k$), let the budget satisfy $n \ge k\lceil\log_2 k\rceil$ (every phase pulls each active arm at least once; implicit in the book's proof), and let $H_2$ be any upper bound of $\{i/\Delta_{(i)}^2 : \Delta_{(i)}>0\}$ — in particular the book's
--
--   $$H_2(\mu) = \max_{i\ne i^*} \frac{i}{\Delta_{(i)}^2}.$$
--
--   If $\pi$ with recommendation rule implements sequential halving (Algorithm 22), then the recommended arm is suboptimal with probability at most
--
--   $$3\log_2(k)\exp\!\left(-\frac{n}{16 H_2\log_2 k}\right).$$
-- source:
--   L&S Theorem 33.10, p.412

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_SequentialHalving


open MeasureTheory

theorem BanditAlgorithm.best_arm_identification_sequential_halving {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (rec : BanditHistory k n → Fin k)
    (hπ : IsSequentialHalvingPolicy k n π rec) :
    (banditMeasure ν π n).real {h | 0 < banditGap ν (rec h)} ≤
      3 * Real.logb 2 k * Real.exp (-(n / (16 * H₂ * Real.logb 2 k))) := by
  sorry
