-- Prove2me | solution 1 for levy_foundations_compoundDriverInterarrivalPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:31:40.82314+00:00
-- url     : https://prove2.me/submissions/fc8d24f4-f7f2-43b9-885c-7ee08c5cc103

import Mathlib
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, ∀ n, 0 < τ n ω := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) := isProbabilityMeasure_expMeasure hr'
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have hset : {ω | ¬ 0 < τ n ω} = (τ n) ⁻¹' (Set.Iic 0) := by
    ext ω; simp [Set.mem_Iic, not_lt]
  rw [hset, ← Measure.map_apply (h.measurable_interarrival n) measurableSet_Iic,
    (h.law_interarrival n).map_eq, ← ofReal_cdf (expMeasure (r : ℝ)) 0,
    cdf_expMeasure_eq hr' 0]
  simp
