-- Prove2me | Theorems.Thm_BanditAlgorithm_moss_pull_count_le_kappa_on_large_gap
-- name    : BanditAlgorithm.moss_pull_count_le_kappa_on_large_gap
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-07-29T02:10:27.989523+00:00
-- url     : https://prove2.me/theorems/6f0bef87-735b-4408-a880-6b63bbb8e757
-- title:
--   $T_i(n) \le \kappa_i$ when $2\tilde\Delta < \Delta_i$
-- statement:
--   Under MOSS, on the event that an arm's suboptimality gap exceeds twice the optimal arm's index shortfall, the arm's pull count is dominated by its MOSS index count:
--
--   $$2\tilde\Delta < \Delta_i \;\Longrightarrow\; T_i(n) \le \kappa_i,$$
--
--   almost surely under the canonical bandit measure. Here $\tilde\Delta$ is the amount by which the optimal arm's MOSS index ever drops below its true mean, and $i^{*}$ is an optimal arm.
--
--   This is the justification given on printed p. 126 of Lattimore--Szepesvári: "for arms $i$ with $\Delta_i > 2\tilde\Delta$, the index of the optimal arm is always larger than $\mu_i + \Delta_i/2$, so $\kappa_i$ is an upper bound on $T_i(n)$." Indeed, whenever MOSS plays arm $i$ its index is maximal, hence at least the optimal arm's index, which on this event exceeds $\mu_i + \Delta_i/2$ — so that pull is counted by $\kappa_i$. The hypothesis is essential: without it the domination genuinely fails.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, proof of Theorem 9.1, printed p. 126 / PDF p. 135: 'for arms i with Delta_i > 2 Delta, the index of the optimal arm is always larger than mu_i + Delta_i/2, so kappa_i is an upper bound on T_i(n)'.

import Definitions.Def_mossKappa
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.moss_pull_count_le_kappa_on_large_gap
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π)
    (iStar : Fin k)
    (hiStar : BanditAlgorithm.banditArmMean ν iStar =
      BanditAlgorithm.banditOptimalMean ν)
    (i : Fin k) :
    ∀ᵐ h ∂(BanditAlgorithm.banditMeasure ν π n),
      2 * BanditAlgorithm.mossOptimalShortfall ν iStar h <
          BanditAlgorithm.banditGap ν i →
        (BanditAlgorithm.armPullCount i h : ℝ) ≤
          (BanditAlgorithm.mossKappa ν i h : ℝ) := by sorry
