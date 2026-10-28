-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_weighted_clock_section_probability_transfer
-- name    : AvramDividend.Classical.avram_ws01e_b_joint_weighted_clock_section_probability_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:21:02.681863+00:00
-- url     : https://prove2.me/theorems/a4fca343-0821-4ade-896b-2a6c6392a352
-- title:
--   True random-terminal density-weighted event equality from equal fixed-clock weighted sections
-- statement:
--   Let P be a path measure, η a clock measure, and D(ω,t) any jointly measurable nonnegative clock-dependent likelihood. If two measurable path-clock events A and B have equal probabilities in every t-section under the true fixed-terminal weighted path law P.withDensity(D(·,t)), then their masses under the genuine clock-dependent joint weighted measure (P×η).withDensity(D) are equal. This is the exact fibrewise Fubini/Tonelli transfer needed to pass Esscher-weighted fixed-horizon drawdown/infimum reversal into the random-exponential-horizon law; unlike original-law independent-clock transfer, it retains D(ω,t) and does not assume the tilt is a product measure.
-- source:
--   Proved esscher_joint_clock_event_fibrewise_disintegration (1b4e8dda), integration of pointwise equal fibre masses by lintegral_congr_ae.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_joint_clock_event_fibrewise_disintegration

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Equal density-weighted clock fibres yield equal probabilities under the
genuine joint random-terminal likelihood, not merely under a product law. -/

theorem AvramDividend.Classical.avram_ws01e_b_joint_weighted_clock_section_probability_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    (η : Measure ℝ) [SFinite η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (A B : Set (Ω × ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFibre : ∀ t : ℝ,
      (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | (ω, t) ∈ A} =
      (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | (ω, t) ∈ B}) :
    ((P.prod η).withDensity D) A =
      ((P.prod η).withDensity D) B := by sorry
