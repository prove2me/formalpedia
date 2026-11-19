-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
-- name    : AvramDividend.Classical.avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:25:30.219357+00:00
-- url     : https://prove2.me/theorems/2c8457f9-31ea-4061-bd7a-513832ff20cc
-- title:
--   Right-continuous real L1 martingale: true bounded-stop integrability and initial conditional centring without a maximal L2 assumption
-- statement:
--   True continuous-time bounded-stop optional sampling for an integrable right-continuous-filtration real martingale with almost surely continuous sample paths and zero initial value. Use finite-range upper stopping clocks, conditional expectations of its fixed integrable horizon terminal value, uniform integrability of conditional expectations, and a.e. continuous path convergence. Do not require Gaussian second moments or assert unconditional centring suffices.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapted : ∀ t : ℝ≥0, Measurable[𝓕.rightCont t] (G t))
    (hZero : ∀ᵐ ω ∂P, G 0 ω = 0)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω))
    (hInt : ∀ t : ℝ≥0, Integrable (G t) P)
    (hCond : ∀ s t : ℝ≥0, s ≤ t →
       ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    Integrable (fun ω => G (τ ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun ω => G (τ ω) ω) ω = 0) := by sorry
