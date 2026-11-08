-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_stopped_condexp_initial_event_zero
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn11_stopped_condexp_initial_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:21:34.510221+00:00
-- url     : https://prove2.me/theorems/ce3b7f87-9695-441b-b691-fb3b03e7406d
-- title:
--   Stopped-filtration conditional centring cancels integrals on arbitrary initial events
-- statement:
--   An integrable random variable with zero conditional expectation at any nonnegative stopping time has zero integral over every event measurable at time zero. Unlike positive-clock masking, this works uniformly for every initial-filtration event and is the bridge from actual Gaussian stopped cells to the original finite-cap budget.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn11_stopped_condexp_initial_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hStoppedZero : ∀ᵐ ω ∂P,
      condExp hτstop.measurableSpace P M ω = 0)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    (∫ ω in A, M ω ∂P) = 0 := by sorry
