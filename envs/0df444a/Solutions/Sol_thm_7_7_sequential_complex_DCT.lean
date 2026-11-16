-- Prove2me | solution 1 for thm_7_7_sequential_complex_DCT
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:50.836896+00:00
-- url     : https://prove2.me/submissions/62ae03e7-94f8-4887-82c7-6b62d4436d48

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology


theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n : ℕ => ∫ ω, Xn n ω ∂μ) atTop
        (nhds (∫ ω, X ω ∂μ)) := by
  have hXm' : AEStronglyMeasurable X μ := aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have hbX : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ Y ω := by
    have hb : ∀ᵐ ω ∂μ, ∀ n, ‖Xn n ω‖ ≤ Y ω := ae_all_iff.mpr h_bound
    filter_upwards [hb, h_lim] with ω hω hl
    exact le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hl) hω
  exact ⟨Integrable.mono' hYint hXm' hbX,
    tendsto_integral_of_dominated_convergence Y hXm hYint h_bound h_lim⟩

