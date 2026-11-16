-- Prove2me | solution 1 for thm_7_DCT_filter
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:51.361844+00:00
-- url     : https://prove2.me/submissions/74913bf7-6e39-472b-86e3-7f0b6b20faf7

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology


/-- Filter-form complex dominated convergence. This is the analytic engine used by
the local interval statement below; the public theorem keeps the source's local
parameter domain instead of requiring global hypotheses on all real parameters. -/
theorem solution {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xh : ι → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (l : Filter ι) [l.IsCountablyGenerated]
    (hXm : ∀ᶠ h in l, AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ᶠ h in l, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) l (nhds (X ω))) :
    Tendsto (fun h => ∫ ω, Xh h ω ∂μ) l
      (nhds (∫ ω, X ω ∂μ)) := by
  exact tendsto_integral_filter_of_dominated_convergence Y hXm h_bound hYint h_lim

