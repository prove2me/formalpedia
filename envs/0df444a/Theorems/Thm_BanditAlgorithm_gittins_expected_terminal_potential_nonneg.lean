-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_expected_terminal_potential_nonneg
-- name    : BanditAlgorithm.gittins_expected_terminal_potential_nonneg
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T17:13:25.829222+00:00
-- url     : https://prove2.me/theorems/c235f05d-60a3-4e70-9e76-f8a2c6635454
-- title:
--   Nonnegativity of expected Gittins terminal potential
-- statement:
--   At every finite horizon, the expected Gittins terminal retirement potential is nonnegative:
--
--   $$
--   0\le U_N^\pi.
--   $$
--
--   This holds for every Markov bandit policy and initial state vector under the discounted absolute-reward integrability assumption. It records the lower bound needed when the terminal term is removed by a squeeze argument.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, retirement-option argument in proof of Lemma 35.10, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_expected_terminal_potential_nonneg
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (N : ℕ) :
    0 ≤ markovBanditExpectedRetirementPotential P r α π x N := by
  sorry
