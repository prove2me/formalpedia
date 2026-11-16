-- Prove2me | solution 1 for thm_7_7_interval
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:52.000701+00:00
-- url     : https://prove2.me/submissions/d33bd4d4-9f9d-45c5-a587-1083da42c02e

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology


theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Set ℝ) (h0 : ℝ)
    (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hh0 : h0 ∈ I)
    (hXm : ∀ h : ℝ, h ∈ I → AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, h ∈ I → ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h : ℝ => Xh h ω) (nhdsWithin h0 I) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h : ℝ => ∫ ω, Xh h ω ∂μ) (nhdsWithin h0 I)
      (nhds (∫ ω, X ω ∂μ)) := by
  have hpure : pure h0 ≤ nhdsWithin h0 I := pure_le_nhdsWithin hh0
  have hEq : ∀ᵐ ω ∂μ, Xh h0 ω = X ω := by
    filter_upwards [h_lim] with ω hl
    have h2 : Tendsto (fun h : ℝ => Xh h ω) (pure h0) (nhds (X ω)) := hl.mono_left hpure
    rw [tendsto_pure_left] at h2
    exact eq_of_forall_dist_le fun ε hε => by
      have := h2 (Metric.closedBall (X ω) ε) (Metric.closedBall_mem_nhds _ hε)
      simpa [dist_comm] using this
  have hint0 : Integrable (Xh h0) μ := Integrable.mono' hYint (hXm h0 hh0) (h_bound h0 hh0)
  refine ⟨hint0.congr hEq, ?_⟩
  exact tendsto_integral_filter_of_dominated_convergence Y
    (eventually_nhdsWithin_of_forall hXm) (eventually_nhdsWithin_of_forall h_bound) hYint h_lim

