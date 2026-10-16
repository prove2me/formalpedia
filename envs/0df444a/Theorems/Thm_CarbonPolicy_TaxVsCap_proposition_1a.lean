-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_proposition_1a
-- name    : CarbonPolicy.TaxVsCap.proposition_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:16.612981+00:00
-- url     : https://prove2.me/theorems/f87d29bf-1112-4f1c-b58d-3d08b095beba
-- title:
--   Proposition 1(a): investment comparison at $R_0$
-- statement:
--   Let $\gamma_T^*$ and $\gamma_C^*$ be arbitrary maximizing emission intensities under the two policies. With $R_0=(\sigma/\sigma_D)\gamma_T^*$, the firm invests more in clean technology under the tax precisely when the correlation is below $R_0$:
--
--   $$\gamma_T^*<\gamma_C^*\quad\Longleftrightarrow\quad\rho<R_0.$$
--
--   Lower emission intensity means greater clean-technology investment. The threshold uses the closed-form tax maximizer from Lemma 1, while the comparison quantifies over arbitrary maximizers.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), p. 15, Proposition 1(a)

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem proposition_1a {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp)
    (γT γC : ℝ) (hT : OptimalTax M b β γp w γT)
    (hC : OptimalCap M b β γp w γC) :
    γT < γC ↔ rho M.P M.a M.k < R0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) := by sorry

end CarbonPolicy.TaxVsCap
