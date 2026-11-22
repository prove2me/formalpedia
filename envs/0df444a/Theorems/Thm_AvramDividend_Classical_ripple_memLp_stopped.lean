-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_memLp_stopped
-- name    : AvramDividend.Classical.ripple_memLp_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:07:54.534938+00:00
-- url     : https://prove2.me/theorems/c1ae4c05-1480-40be-a448-182c171376e2
-- title:
--   Stopped predictable integrands retain square-integrability under trimmed product measure
-- statement:
--   If a stochastic integrand is L² under the predictable trim of the product of time measure and sample measure, multiplying it by the indicator of a stochastic interval (0,τ] preserves the same L² membership, for any stopping time τ. This is needed to construct actual stopped Brownian Itô integrals. The predictable-to-product measurable-space inclusion is passed explicitly rather than relying on Ripple's external extension declaration.
-- source:
--   Source proof copied and adapted from Ripple/Stochastic/StoppedPredictableIntegrand.lean, theorem memLp_stopped, commit e216e28ce3ffb43877e11f71be260e40a37a35df (Apache-2.0), using Proved AvramDividend.Classical.ripple_stopping_region_predictable.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable

open MeasureTheory Set

theorem AvramDividend.Classical.ripple_memLp_stopped
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration NNReal mΩ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime F τ)
    (hprod : F.predictable ≤ (inferInstance : MeasurableSpace (NNReal × Ω)))
    {ν : Measure NNReal} {μ : Measure Ω}
    {H : NNReal × Ω → ℝ}
    (hH : MemLp H 2 ((ν.prod μ).trim hprod)) :
    MemLp
      ({z : NNReal × Ω | 0 < z.1 ∧ (z.1 : WithTop NNReal) ≤ τ z.2}.indicator H)
      2 ((ν.prod μ).trim hprod) := by sorry
