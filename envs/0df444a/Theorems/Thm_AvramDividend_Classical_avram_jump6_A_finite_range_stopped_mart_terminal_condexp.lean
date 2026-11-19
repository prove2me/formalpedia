-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_finite_range_stopped_mart_terminal_condexp
-- name    : AvramDividend.Classical.avram_jump6_A_finite_range_stopped_mart_terminal_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:39:15.100808+00:00
-- url     : https://prove2.me/theorems/95460b30-bb00-421e-a912-99be5f387048
-- title:
--   Finite-range true bounded stopping time is terminal conditional sample of its same-filtration real martingale
-- statement:
--   For the original right-continuous filtration, a finite-range bounded stopping time applied to an integrable adapted real martingale equals conditional expectation of the true fixed-horizon terminal source relative to the stopping sigma algebra. Apply exact Mathlib optional sampling with finite countable stopping range. No independence or fake Gaussian representation.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_finite_range_stopped_mart_terminal_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapted : ∀ t : ℝ≥0, Measurable[𝓕.rightCont t] (G t))
    (hInt : ∀ t : ℝ≥0, Integrable (G t) P)
    (hCond : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hBound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hS : ∀ ω, ρ ω ∈ S) :
    (fun ω => G (ρ ω) ω) =ᵐ[P]
      condExp hStop.measurableSpace P (G (n : ℝ≥0)) := by sorry
