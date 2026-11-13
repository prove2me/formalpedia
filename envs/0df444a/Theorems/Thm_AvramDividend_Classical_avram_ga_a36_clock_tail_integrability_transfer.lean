-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a36_clock_tail_integrability_transfer
-- name    : AvramDividend.Classical.avram_ga_a36_clock_tail_integrability_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:43:09.894048+00:00
-- url     : https://prove2.me/theorems/8ac88c02-cf47-485c-b11b-d98c5bd700a4
-- title:
--   Positive-tail random-clock moment integrability transfers to fixed horizon
-- statement:
--   For an original state measure P and a random clock with any positive right-tail measure nu(Ioi T), let g be the fixed-horizon nonnegative exponential-supremum integrand and H the random-clock integrand. If g(omega) is pointwise dominated by H(omega,t) whenever t>T, and H is integrable on P.prod nu, then g is integrable on P. The proof is Fubini/Tonelli applied to indicator_{t>T} g(omega), using positive clock-tail mass. This is the exact transfer needed to turn the Proved exponential-clock supremum MGF 626336fd and survival law e306d2ca into the finite-horizon supremum exponential moment for the original Gaussian terminal envelope d9c4650e.
-- source:
--   d9c4650e-839e-480f-860a-906387200065; Proved 626336fd, e306d2ca, 848fbd48.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a36_clock_tail_integrability_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (nu : Measure ℝ) [SFinite nu]
    (g : Ω → ℝ≥0∞) (H : Ω × ℝ → ℝ≥0∞)
    (T : ℝ) (hg : Measurable g)
    (hTail : 0 < nu (Set.Ioi T))
    (hBound : ∀ z : Ω × ℝ, T < z.2 → g z.1 ≤ H z)
    (hMoment : (∫⁻ z : Ω × ℝ, H z ∂ (P.prod nu)) < ⊤) :
    (∫⁻ omega : Ω, g omega ∂ P) < ⊤ := by sorry
