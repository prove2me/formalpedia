-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_lemma_1
-- name    : CarbonPolicy.TaxVsCap.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:07.484975+00:00
-- url     : https://prove2.me/theorems/195388a1-a380-460e-b742-91bb0ec69b6f
-- title:
--   Lemma 1: unique optimal intensity under the carbon tax
-- statement:
--   Under Assumption 1 and the standing conditions, the unique optimal emission intensity under the carbon tax is
--
--   $$\gamma_T^*=\frac{4b\beta\gamma^+-\bar a\bar k}{4b\beta-\bar k^2}.$$
--
--   Optimality means maximizing the expected tax profit $\Pi_T$ over $[0,\gamma^+]$. The formula identifies the investment decision for every admissible demand and permit-price distribution with these moments.
--
--   **Formalization Note** The theorem states both that the displayed intensity is a maximizer and that every maximizer equals it.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), p. 12, Lemma 1 and equation (4)

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem lemma_1 {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp) :
    OptimalTax M b β γp w (gammaT0 b β γp (abar M.P M.a) (kbar M.P M.k)) ∧
    ∀ γ : ℝ, OptimalTax M b β γp w γ → γ = gammaT0 b β γp (abar M.P M.a) (kbar M.P M.k) := by sorry

end CarbonPolicy.TaxVsCap
