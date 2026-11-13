-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
-- name    : AvramDividend.Classical.avram_b21_initial_event_local_aggregate_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:56:56.527372+00:00
-- url     : https://prove2.me/theorems/65038621-bd04-4f66-8a7a-d49deb781a56
-- title:
--   Original initial-event aggregate stopped cash budget without separate global noise moments
-- statement:
--   A ruin-stopped cash reward bounded by initial test value, one aggregate gain with zero mean on the initial-filtration event, and an integrable signed error inherits a local eventwise expected upper bound. Only event-restricted L1, rather than independent global noise channel moments, is required.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i), stopped Ito-Meyer localisation. Direct restricted-integral inequality; original physical one-cell source estimate remains separate.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b21_initial_event_local_aggregate_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F M Err : Ω → ℝ)
    (hFI : IntegrableOn F A P)
    (hMI : IntegrableOn M A P)
    (hEI : IntegrableOn Err A P)
    (hMzero : (∫ ω in A, M ω ∂P) = 0)
    (hUpper : ∀ᵐ ω ∂(P.restrict A), F ω ≤ b + M ω + Err ω) :
    (∫ ω in A, F ω ∂P) ≤
      b * (P A).toReal + (∫ ω in A, Err ω ∂P) := by sorry
