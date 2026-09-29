-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_accounting
-- name    : BanditAlgorithm.gittins_finite_prevailing_charge_accounting
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T16:19:00.523385+00:00
-- url     : https://prove2.me/theorems/1b9128d6-09c5-4a71-b11d-b1841af38531
-- title:
--   Finite prevailing-charge accounting identities
-- statement:
--   Under discounted absolute-reward integrability, compare finite reward and prevailing charge over a horizon $N$.  For every policy $\pi$, finite discounted reward is at most its finite discounted prevailing-charge value.  If $\pi^*$ is a Gittins-index policy, its charge accounting is exact up to the terminal retirement potential:
--
--   $$
--   R_N^\pi\le C_N^\pi,
--   \qquad
--   C_N^{\pi^*}=R_N^{\pi^*}+\alpha^N U_N^{\pi^*}.
--   $$
--
--   This is Part 1 of the prevailing-charge proof and is reusable independently of the greedy interleaving argument.
--
--   **Formalization Note** Both assertions are bundled so the arbitrary-policy Bellman inequality and the fair-charge identity share the same horizon and initial state.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, §35.4, proof of Theorem 35.9, Part 1 “Prevailing Charge”, printed pp. 451–452 / PDF pp. 459–460.

import Definitions.Def_GittinsPrevailingChargeValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_finite_prevailing_charge_accounting
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
        markovBanditFinitePrevailingChargeValue P r α π x N ∧
      markovBanditFinitePrevailingChargeValue P r α πstar x N =
        (∑ n ∈ Finset.range N,
          α ^ n * markovBanditRoundReward P r πstar x n) +
        α ^ N * markovBanditExpectedRetirementPotential
          P r α πstar x N := by
  sorry
