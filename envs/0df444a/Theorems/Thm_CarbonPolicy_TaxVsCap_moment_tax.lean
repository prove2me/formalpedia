-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_moment_tax
-- name    : CarbonPolicy.TaxVsCap.moment_tax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:09.358262+00:00
-- url     : https://prove2.me/theorems/f9233800-2537-4009-9c3d-29609d9a6193
-- title:
--   Expected-profit moment form under the carbon tax
-- statement:
--   For every emission intensity $\gamma$, expected profit under the fixed carbon tax equals
--
--   $$\Pi_T(\gamma)=\frac{(\bar a-\gamma\bar k)^2+\sigma_D^2}{4b}-\beta(\gamma^+-\gamma)^2+w\bar k.$$
--
--   This is the moment form of the expectation-based first-stage tax objective in the proof of Lemma 1. Demand potential and permit price are in $L^2$, and $b>0$.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), Online Appendix C.1, p. 8 (PDF 44), proof of Lemma 1

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem moment_tax {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiT M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) - β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by sorry

end CarbonPolicy.TaxVsCap
