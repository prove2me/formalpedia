-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_lemma_2
-- name    : CarbonPolicy.TaxVsCap.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:10.963966+00:00
-- url     : https://prove2.me/theorems/8d00bf39-ec1d-4d9f-9b6a-94d596400932
-- title:
--   Lemma 2: unique optimal intensity under cap-and-trade
-- statement:
--   Under Assumption 1 and the standing conditions, the unique optimal emission intensity under cap-and-trade is
--
--   $$\gamma_C^*=\begin{cases}\dfrac{4b\beta\gamma^+-\bar a\bar k-\rho\sigma_D\sigma}{4b\beta-\bar k^2-\sigma^2},&\bar a\bar k+\rho\sigma_D\sigma>(\bar k^2+\sigma^2)\gamma^+,\\\gamma^+,&\bar a\bar k+\rho\sigma_D\sigma\le(\bar k^2+\sigma^2)\gamma^+.\end{cases}$$
--
--   The second branch is the boundary solution to the first-stage cap-and-trade problem on $[0,\gamma^+]$.
--
--   **Formalization Note** The theorem states both existence and uniqueness of the maximizing intensity.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), p. 12, Lemma 2 and equation (5)

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem lemma_2 {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp) :
    OptimalCap M b β γp w (gammaC0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) (rho M.P M.a M.k)) ∧
    ∀ γ : ℝ, OptimalCap M b β γp w γ → γ = gammaC0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) (rho M.P M.a M.k) := by sorry

end CarbonPolicy.TaxVsCap
