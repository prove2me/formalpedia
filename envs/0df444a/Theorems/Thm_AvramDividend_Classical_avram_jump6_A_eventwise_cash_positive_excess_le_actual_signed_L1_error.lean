-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_eventwise_cash_positive_excess_le_actual_signed_L1_error
-- name    : AvramDividend.Classical.avram_jump6_A_eventwise_cash_positive_excess_le_actual_signed_L1_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:23:30.96961+00:00
-- url     : https://prove2.me/theorems/93a40f8c-1c93-49c4-87c8-66889b36814b
-- title:
--   Eventwise realised original cash positive excess controlled by signed physical Ito remainder in L1
-- statement:
--   If a stopped physical Ito cash ledger bounds realised reward by the initial HJB value plus Gaussian and compensated nonlinear marked gains and a signed integrable remainder, then the expected positive excess of reward over initial value and gains is bounded by the eventwise L1 norm of the remainder. This isolates a reusable deterministic-to-L1 verification step without assuming the stochastic remainder has a sign.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_eventwise_cash_positive_excess_le_actual_signed_L1_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (F G J E : Ω → ℝ) (w : ℝ)
    (hFI : IntegrableOn F A P) (hGI : IntegrableOn G A P)
    (hJI : IntegrableOn J A P) (hEI : IntegrableOn E A P)
    (hBound : ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ w + G ω + J ω + E ω) :
    (∫ ω in A, max (F ω - w - G ω - J ω) 0 ∂P) ≤
      (∫ ω in A, |E ω| ∂P) := by sorry
