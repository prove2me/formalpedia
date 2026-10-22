-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_emission_difference
-- name    : CarbonPolicy.TaxVsCap.emission_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:11.955013+00:00
-- url     : https://prove2.me/theorems/e258af0d-9e31-4237-8d85-4f035835440d
-- title:
--   Online Appendix C.1: expected-emissions difference
-- statement:
--   For any tax and cap-and-trade emission intensities $\gamma_T,\gamma_C$, the difference between their expected emissions is
--
--   $$S_T-S_C=\frac{(\gamma_T-\gamma_C)(\bar a-(\gamma_T+\gamma_C)\bar k)}{2b}.$$
--
--   Its two factors determine the emission comparison in Corollary 1(b). The identity does not require the intensities to be maximizers.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), Online Appendix C.1, p. 13 (PDF 49), proof of Corollary 1

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem emission_difference {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b γT γC : ℝ) (hb : 0 < b) :
    ST M b γT - SC M b γC =
      (γT - γC) * ((abar M.P M.a) - (γT + γC) * (kbar M.P M.k)) / (2 * b) := by sorry

end CarbonPolicy.TaxVsCap
