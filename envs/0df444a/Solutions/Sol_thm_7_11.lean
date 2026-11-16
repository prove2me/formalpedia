-- Prove2me | solution 1 for thm_7_11
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:49.630189+00:00
-- url     : https://prove2.me/submissions/c5f41507-5937-4a34-8001-3fe3bed677d2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory


/--
  ## Theorem 7.11
for a measurable `X : Ω → ℝ`, integrability of `h ∘ X` under
`μ` is equivalent to integrability of `h` under the pushforward
measure `Measure.map X μ`, and the corresponding integrals agree.
-/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ} (hX : Measurable X) (hh : Measurable h) :
    (Integrable (fun ω => h (X ω)) μ ↔ Integrable h (Measure.map X μ)) ∧
      (∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ) := by
  exact ⟨(integrable_map_measure hh.aestronglyMeasurable hX.aemeasurable).symm,
    (integral_map hX.aemeasurable hh.aestronglyMeasurable).symm⟩

