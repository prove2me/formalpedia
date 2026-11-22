-- Prove2me | Theorems.Thm_AvramDividend_Classical_ftap_condExp_ae_eq_of_uniformIntegrable_tendsto
-- name    : AvramDividend.Classical.ftap_condExp_ae_eq_of_uniformIntegrable_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:47:50.880477+00:00
-- url     : https://prove2.me/theorems/d0b5a6ef-a843-4f93-a3c6-d8872c336dd8
-- title:
--   Uniform-integrability passage to a common stopped conditional expectation, adapted from FTAP
-- statement:
--   For a uniformly integrable family of real terminal values that converges almost everywhere, equality of every conditional expectation to the same measurable integrable random variable passes to the limit. This supplies a narrowly scoped route for removing localisation after the Avram original process stochastic source has been constructed and uniform integrability verified. Adapted from Mocho Go, FTAPTheorem42/Stochastic/Martingale/Basic/BoundedStoppingOptionalSampling.lean, git commit 8c9c46e1b6e455f7d3069062957d4363879836ce, Apache-2.0.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/Martingale/Basic/BoundedStoppingOptionalSampling.lean

import Mathlib
open Filter MeasureTheory Set Topology
open scoped MeasureTheory NNReal

theorem AvramDividend.Classical.ftap_condExp_ae_eq_of_uniformIntegrable_tendsto
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim (m := m) hm)]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hfUI : UniformIntegrable f 1 μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (c : Ω → ℝ) (_hcMeas : AEStronglyMeasurable[m] c μ)
    (hcond : ∀ n, μ[f n | m] =ᵐ[μ] c) :
    μ[g | m] =ᵐ[μ] c := by sorry
