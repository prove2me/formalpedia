-- Prove2me | solution 1 for thm_7_7
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:52.614834+00:00
-- url     : https://prove2.me/submissions/aeff2e5c-38c7-463a-af9a-896c514bff0f

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology


/-- Compatibility helper for the existing global real-parameter specialization. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (h0 : ℝ)
    (hXm : ∀ h : ℝ, AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) (nhds h0) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h => ∫ ω, Xh h ω ∂μ) (nhds h0) (nhds (∫ ω, X ω ∂μ)) := by
  have hpure : pure h0 ≤ nhds h0 := pure_le_nhds h0
  have hEq : ∀ᵐ ω ∂μ, Xh h0 ω = X ω := by
    filter_upwards [h_lim] with ω hl
    have h2 : Tendsto (fun h : ℝ => Xh h ω) (pure h0) (nhds (X ω)) := hl.mono_left hpure
    rw [tendsto_pure_left] at h2
    exact eq_of_forall_dist_le fun ε hε => by
      have := h2 (Metric.closedBall (X ω) ε) (Metric.closedBall_mem_nhds _ hε)
      simpa [dist_comm] using this
  have hint0 : Integrable (Xh h0) μ := Integrable.mono' hYint (hXm h0) (h_bound h0)
  refine ⟨hint0.congr hEq, ?_⟩
  exact tendsto_integral_filter_of_dominated_convergence Y
    (Filter.Eventually.of_forall hXm) (Filter.Eventually.of_forall h_bound) hYint h_lim

