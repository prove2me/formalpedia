-- Prove2me | solution 1 for levy_foundations_compoundDriverArrivalMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:06:56.534087+00:00
-- url     : https://prove2.me/submissions/a313e43b-f8cb-4aa9-ba8c-32a569ca70aa

import Mathlib
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Source-exact finite-sum measurability of a compound driver's arrival. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (n : ℕ) :
    Measurable (LevyFoundations.arrival τ n) := by
  change Measurable (fun ω => ∑ i ∈ Finset.range (n + 1), τ i ω)
  exact Finset.measurable_sum _ fun i _ => h.measurable_interarrival i
