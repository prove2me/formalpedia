-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_index_theorem
-- name    : BanditAlgorithm.gittins_index_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T15:43:21.800057+00:00
-- url     : https://prove2.me/theorems/52a4067f-d6cc-475f-96a3-71302ac02eee
-- statement:
--   (Gittins index theorem, L&S Theorem 35.9) For the infinite-horizon $\alpha$-discounted $k$-armed Markov bandit on a Borel state space, assume the integrability Assumption 35.6:
--
--   $$\mathbb{E}_x\Big[\sum_t \alpha^{t-1}|r(S_t)|\Big] < \infty \quad\text{for every state } x$$
--
--   (hence for all the Markov chains of the game). Then every Gittins index policy $\pi^*$ (activating an arm of maximal index each round, ties arbitrary) attains the supremum of the expected total discounted reward over all policies:
--
--   $$\mathbb{E}_{\pi^*}\!\left[\sum_{t=1}^\infty \alpha^{t-1} r(S_{A_t}(t))\right] = \sup_\pi\, \mathbb{E}_\pi\!\left[\sum_{t=1}^\infty \alpha^{t-1} r(S_{A_t}(t))\right].$$
-- source:
--   L&S Theorem 35.9, p.450

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex


open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_index_theorem {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (πstar : MarkovBanditPolicy k S) (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    markovBanditDiscountedValue P r α πstar x =
      ⨆ π : MarkovBanditPolicy k S, markovBanditDiscountedValue P r α π x := by
  sorry
