-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:48:35.388196+00:00
-- url     : https://prove2.me/theorems/e5cc5d15-ff9b-4dd7-b1c2-304194654161
-- title:
--   Original Lévy quadratic small-negative-jump compensator tail vanishes at zero cutoff
-- statement:
--   The original source Lévy measure X.ν satisfies a zero limit for the squared-mark compensator integral over the shrinking negative strip (-1/(n+1),0]. This follows without auxiliary processes from X.ν_integrable, since on |z|≤1 the Lévy density integrand min(1,z²) equals z² and dominates the varying strip indicators. It is the exact quantitative small-jump tail needed to obtain a source L2 Cauchy estimate after the original stochastic isometry is proved.
-- source:
--   Original SpectrallyNegativeLevy ν_integrable and pinned Mathlib MeasureTheory.tendsto_lintegral_of_dominated_convergence; the reciprocal cutoff tends to zero by pinned tendsto_one_div_add_atTop_nhds_zero_nat. No stochastic compensation assertion is assumed.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      ∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν) atTop (𝓝 0) := by sorry
