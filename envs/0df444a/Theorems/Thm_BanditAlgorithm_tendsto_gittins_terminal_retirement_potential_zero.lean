-- Prove2me | Theorems.Thm_BanditAlgorithm_tendsto_gittins_terminal_retirement_potential_zero
-- name    : BanditAlgorithm.tendsto_gittins_terminal_retirement_potential_zero
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T15:54:19.79244+00:00
-- url     : https://prove2.me/theorems/604bdfbb-b89b-434c-93f0-f794e0a98f14
-- title:
--   Vanishing discounted terminal retirement potential
-- statement:
--   Consider a finite-armed rested Markov bandit with measurable rewards and discount factor $0<\alpha<1$.  Under discounted absolute-reward integrability, the expected retirement potential at the prevailing charges grows slowly enough that its discounted terminal contribution vanishes:
--
--   $$
--   \alpha^N U_N^\pi \longrightarrow 0
--   \qquad (N\to\infty)
--   $$
--
--   for every policy $\pi$ and every initial state vector.
--
--   This theorem supplies the uniform-integrability tail step needed to pass from the finite prevailing-charge inequality to infinite-horizon Gittins optimality.
--
--   **Formalization Note** The conclusion is convergence in $\mathbb R$ along `Filter.atTop`; no bounded-reward assumption is imposed beyond the platform's formalization of Assumption 35.6.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, Assumption 35.6 and §35.4 proof of Theorem 35.9, terminal passage after Parts 1–2, printed pp. 447 and 451–453 / PDF pp. 455 and 459–461.

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.tendsto_gittins_terminal_retirement_potential_zero
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    Filter.Tendsto (fun N ↦ α ^ N *
      markovBanditExpectedRetirementPotential P r α π x N)
      Filter.atTop (nhds 0) := by
  sorry
