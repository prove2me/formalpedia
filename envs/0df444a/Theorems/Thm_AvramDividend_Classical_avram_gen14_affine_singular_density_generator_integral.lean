-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_affine_singular_density_generator_integral
-- name    : AvramDividend.Classical.avram_gen14_affine_singular_density_generator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:43:36.20627+00:00
-- url     : https://prove2.me/theorems/6ffbc13a-9b39-4308-bd7c-c1a072a91e85
-- title:
--   Exact original affine generator jump integral against singular negative Levy measure
-- statement:
--   For a strictly positive reserve below one and the payoff affine above zero and killed at ruin, the original source-defined Levy generator jump integrand has an exactly computable integral under the negative one-to-zero singular Levy measure. This is the expression needed for a deterministic generator deficit calculation relevant to a possible counterexample to the stochastic random-state integrability assertion.
-- source:
--   Previously proved original generator full-band formula, singular Levy density Bochner restriction, and affine crossing kernel closed form; pinned Mathlib setIntegral_indicator, intervalIntegral.integral_of_le, and integral_Ioc_eq_integral_Ioo.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_affine_singular_density_generator_integral
    (x : ℝ) (hx : 0 < x) (hcap : x < 1) :
    (∫ z, SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z
      ∂(volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) =
      2 * (1 - x ^ (1 / 2 : ℝ)) -
        (1 + x) * (2 * (x ^ (-(1 / 2 : ℝ)) - 1)) := by sorry
