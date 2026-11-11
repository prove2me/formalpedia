-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite36_event_integral_upper_from_vanishing_error
-- name    : AvramDividend.Classical.avram_gfinite36_event_integral_upper_from_vanishing_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:47:45.640495+00:00
-- url     : https://prove2.me/theorems/c2574632-d41f-4170-926e-d591ae3afa8b
-- title:
--   Eventwise upper integral bound from centred approximating martingale and vanishing source error
-- statement:
--   For a finite measure, if an integrable physical payoff on an event is bounded almost surely by a constant initial reward plus integrable centred mesh residuals and integrable errors whose event integrals tend to zero, then its event integral is bounded by the constant-reward integral. The theorem is a direct Bochner integral monotonicity and limit passage used to turn original-process Gaussian mesh certificates into the Avram stopped cash budget.
-- source:
--   Finite Gaussian mesh-to-physical deterministic bridge for original finite-cap source child 40ec25bd. It does not assume an Ito budget: the source certificate must separately construct M and E with pointwise upper inequality, zero mean on each initial event, and physical vanishing integral error.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite36_event_integral_upper_from_vanishing_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (b : ℝ) (F : Ω → ℝ)
    (M E : ℕ → Ω → ℝ)
    (hFI : IntegrableOn F A P)
    (hMI : ∀ n, IntegrableOn (M n) A P)
    (hEI : ∀ n, IntegrableOn (E n) A P)
    (hMean : ∀ n, (∫ ω in A, M n ω ∂P) = 0)
    (hUpper : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ b + M n ω + E n ω)
    (hErr : Tendsto (fun n => ∫ ω in A, E n ω ∂P) atTop (𝓝 (0 : ℝ))) :
    (∫ ω in A, F ω ∂P) ≤ ∫ ω in A, (b : ℝ) ∂P := by sorry
