-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniformIntegrable_integral_mass_one_of_ae_tendsto
-- name    : AvramDividend.Classical.uniformIntegrable_integral_mass_one_of_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:11:47.914413+00:00
-- url     : https://prove2.me/theorems/a641544b-c2b0-4f1c-902a-c3ba941f7879
-- title:
--   Mass-one conservation for a.e. limits of uniformly integrable real densities on finite measure spaces
-- statement:
--   If real densities f_n have integral one, form a uniformly integrable family in L1 under a finite measure and converge almost everywhere to g, then g also has integral one. This is the general analytic Vitali ingredient needed for bounded-stopping-time Esscher optional-sampling limits; no stochastic identities are assumed.
-- source:
--   Pinned Mathlib UniformIntegrable.lean (integrable_of_ae_tendsto, tendsto_Lp_finite_of_tendsto_ae, eLpNorm_one_eq_lintegral_enorm), pinned Mathlib tendsto_integral_of_L1 and uniqueness of limits; no Wiener-Hopf source needed for this pure measure-theoretic statement.

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.uniformIntegrable_integral_mass_one_of_ae_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hUI : UniformIntegrable f 1 μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hmass : ∀ n, (∫ ω, f n ω ∂μ) = (1 : ℝ)) :
    (∫ ω, g ω ∂μ) = (1 : ℝ) := by sorry
