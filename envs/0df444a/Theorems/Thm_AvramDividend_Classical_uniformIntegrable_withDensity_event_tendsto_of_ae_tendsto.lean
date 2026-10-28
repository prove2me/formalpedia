-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
-- name    : AvramDividend.Classical.uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:44:55.86852+00:00
-- url     : https://prove2.me/theorems/e7cacf8f-972f-42a9-a960-08e2276f91d3
-- title:
--   Eventwise convergence of nonnegative withDensity measures under uniformly integrable a.e. convergence
-- statement:
--   For nonnegative real densities f_n that are uniformly integrable in L1 on a finite measure space and converge a.e. to nonnegative g, the probability masses of every measurable event A under μ.withDensity f_n converge to those under μ.withDensity g. This avoids a global Esscher process and is a precise eventwise transfer tool for bounded stopping-time density limits.
-- source:
--   Pinned Mathlib UniformIntegrable.integrable_of_ae_tendsto, tendsto_Lp_finite_of_tendsto_ae, tendsto_setIntegral_of_L1, ofReal_integral_eq_lintegral_ofReal, withDensity_apply and ENNReal.tendsto_ofReal.

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hUI : UniformIntegrable f 1 μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hpos : ∀ n ω, 0 ≤ f n ω) (hgpos : ∀ ω, 0 ≤ g ω)
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun n => (μ.withDensity
      (fun ω => ENNReal.ofReal (f n ω))) A)
      atTop (𝓝 ((μ.withDensity
        (fun ω => ENNReal.ofReal (g ω))) A)) := by sorry
