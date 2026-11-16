-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_event_independent_surrogate_gain_mean_zero
-- name    : AvramDividend.Classical.avram_b27_event_independent_surrogate_gain_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:16:00.040236+00:00
-- url     : https://prove2.me/theorems/933e918e-06f3-4aaa-88a8-86ce91587762
-- title:
--   On a no-large-jump event, a physical gain agreeing with an independent centred Brownian surrogate has zero restricted mean
-- statement:
--   For a measurable event A in a sub-sigma algebra m and each integrable centred random variable H_n whose generated sigma-algebra is independent of m, any physical mesh random variable G_n agreeing with H_n on A has zero restricted expectation on A. In the B25 counterexample the event is zero large Poisson jumps, and H_n is the pure Brownian stopped physical sum formed after setting the Poisson path to zero. Isolates the exact event-product independence and on-event pathwise-identification obligations.
-- source:
--   Original Avram B25 two-channel ruinclipped Gaussian source 78ac3aee and B27 no-large-jump obstruction; Mathlib ProbabilityTheory.Indep.setIntegral_eq_mul.

import Mathlib
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_b27_event_independent_surrogate_gain_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[m] A)
    (G H : ℕ → Ω → ℝ)
    (hHI : ∀ n, Integrable (H n) P)
    (hInd : ∀ n,
      ProbabilityTheory.Indep m
        (MeasurableSpace.comap (H n) inferInstance) P)
    (hSame : ∀ n, ∀ᵐ ω ∂(P.restrict A), G n ω = H n ω)
    (hZero : ∀ n, (∫ ω, H n ω ∂P) = 0) :
    ∀ n, (∫ ω in A, G n ω ∂P) = 0 := by sorry
