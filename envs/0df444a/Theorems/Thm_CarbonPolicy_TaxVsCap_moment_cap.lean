-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_moment_cap
-- name    : CarbonPolicy.TaxVsCap.moment_cap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:08.817989+00:00
-- url     : https://prove2.me/theorems/c667174d-a9a2-480c-85b9-e59b83ec42a0
-- title:
--   Expected-profit moment form under cap-and-trade
-- statement:
--   For every emission intensity $\gamma$, expected profit under cap-and-trade equals
--
--   $$\Pi_C(\gamma)=\frac{(\bar a-\gamma\bar k)^2+\sigma_D^2+\gamma^2\sigma^2-2\gamma\rho\sigma_D\sigma}{4b}-\beta(\gamma^+-\gamma)^2+w\bar k.$$
--
--   This is the moment form of the expectation-based first-stage cap-and-trade objective in the proof of Lemma 2. It records the effect of permit-price variance and demand–price covariance. The random inputs lie in $L^2$ and $b>0$.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), Online Appendix C.1, p. 8 (PDF 44), proof of Lemma 2

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem moment_cap {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiC M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) +
        (γ ^ 2 * (sigma M.P M.k) ^ 2 - 2 * γ * (rho M.P M.a M.k) *
          (sigmaD M.P M.a) * (sigma M.P M.k)) / (4 * b) -
        β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by sorry

end CarbonPolicy.TaxVsCap
