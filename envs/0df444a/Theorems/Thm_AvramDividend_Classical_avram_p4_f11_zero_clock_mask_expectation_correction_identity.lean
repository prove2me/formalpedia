-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_clock_mask_expectation_correction_identity
-- name    : AvramDividend.Classical.avram_p4_f11_zero_clock_mask_expectation_correction_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:51:58.009439+00:00
-- url     : https://prove2.me/theorems/ec52b60b-d12a-438a-ad4d-0e0446b2befa
-- title:
--   Exact L1 correction of the zero-clock payoff mask in the original finite measure
-- statement:
--   For an integrable real payoff F on a finite measure space and a measurable event A, the expected payoff after replacing F by b on A equals its original expected payoff plus the integral over A of b-F. The needed propositional decidability instance is explicit and may be furnished classically by downstream users.
-- source:
--   Bochner integral additivity, indicator of measurable set, exact conditional masked-reward correction.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_zero_clock_mask_expectation_correction_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    [DecidablePred (fun ω : Ω => ω ∈ A)]
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if ω ∈ A then b else F ω) ∂P) =
      (∫ ω, F ω ∂P) + ∫ ω in A, b - F ω ∂P := by sorry
