-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_interleaving
-- name    : BanditAlgorithm.gittins_finite_prevailing_charge_interleaving
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T16:19:24.285838+00:00
-- url     : https://prove2.me/theorems/c3d671aa-d3f6-4d7b-8e16-757cf566c64b
-- title:
--   Finite prevailing-charge comparison for a Gittins policy
-- statement:
--   Let $\pi^*$ be a Gittins-index policy in a finite-armed rested Markov bandit.  For every competing policy $\pi$ and finite horizon $N$, the expected discounted prevailing-charge value of $\pi$ is at most that of $\pi^*$:
--
--   $$
--   C_N^\pi\le C_N^{\pi^*}.
--   $$
--
--   This is the finite probabilistic form of Part 2 of the Gittins proof.  It combines the common independent reward-stack coupling with the deterministic fact that greedily interleaving nonincreasing charge stacks maximizes every discounted finite prefix.
--
--   **Formalization Note** The statement exposes only the finite charge-value interface; reward-stack sample spaces and action likelihoods remain internal proof machinery.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, §35.4, proof of Theorem 35.9, Part 2, printed pp. 452–453 / PDF pp. 460–461, using Lemma 35.10 on printed p. 451 / PDF p. 459.

import Definitions.Def_GittinsPrevailingChargeValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_finite_prevailing_charge_interleaving
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π πstar : MarkovBanditPolicy k S)
    (hπstar : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (N : ℕ) :
    markovBanditFinitePrevailingChargeValue P r α π x N ≤
      markovBanditFinitePrevailingChargeValue P r α πstar x N := by
  sorry
