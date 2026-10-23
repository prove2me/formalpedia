-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_proposition_2a
-- name    : CarbonPolicy.TaxVsCap.proposition_2a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:11.150025+00:00
-- url     : https://prove2.me/theorems/120444d5-40f9-4344-9579-d84f58d66215
-- title:
--   Proposition 2(a): expected-profit comparison at $R$
-- statement:
--   Let $\gamma_T^*,\gamma_C^*$ maximize the two expected-profit objectives. With $R$ given by Proposition 2(a)'s piecewise choice between the smaller quadratic root $\rho_0$ and the corner-branch root $\rho_1$, the threshold satisfies $0<R<R_0$ and
--
--   $$\Pi_T(\gamma_T^*)>\Pi_C(\gamma_C^*)\quad\Longleftrightarrow\quad\rho>R.$$
--
--   This is the firm's expected-profit comparison. The threshold is computed from the model's moments, rather than selected separately for each correlation.
--
--   **Formalization Note** The root $\rho_0$ is the one below $(4b\beta\gamma^+-\bar a\bar k)/(\sigma_D\sigma)$, as required by the proof's domain.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), p. 18, Proposition 2(a)

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem proposition_2a {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp)
    (γT γC : ℝ) (hT : OptimalTax M b β γp w γT)
    (hC : OptimalCap M b β γp w γC) :
    0 < R b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) ∧ R b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) < R0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) ∧
    (PiC M b β γp w γC < PiT M b β γp w γT ↔
      R b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) < rho M.P M.a M.k) := by sorry

end CarbonPolicy.TaxVsCap
