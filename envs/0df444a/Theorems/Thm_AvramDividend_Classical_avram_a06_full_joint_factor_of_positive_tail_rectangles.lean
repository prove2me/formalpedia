-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_full_joint_factor_of_positive_tail_rectangles
-- name    : AvramDividend.Classical.avram_a06_full_joint_factor_of_positive_tail_rectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:50:02.2553+00:00
-- url     : https://prove2.me/theorems/b77ad3ff-3466-40f0-9dbf-290fbfbda5f0
-- title:
--   Positive residual tail rectangles imply full Borel independence of the residual and future suffix pair
-- statement:
--   A positive almost surely real random variable R and measurable future state F form a pair independent of a measurable past event H when every residual-survival upper-halfline crossed with every future measurable set factors with P(H). Use R>0 to extend the factorisation to all real upper half-lines; finite-real measure uniqueness gives all Borel first-coordinate sets and Mathlib Measure.ext_prod gives all measurable pair events. This abstracts the Borel uniqueness step in the original a.e exponential renewal proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_finite_real_measures_eq_of_Ioi
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_full_joint_factor_of_positive_tail_rectangles
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R)
    (F : Ω → E) (hF : Measurable F)
    (H : Set Ω) (hH : MeasurableSet H)
    (hPos : ∀ᵐ ω ∂P, 0 < R ω)
    (hTail : ∀ (u : ℝ), 0 ≤ u → ∀ (B : Set E),
      MeasurableSet B →
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B})
    (D : Set (ℝ × E)) (hD : MeasurableSet D) :
    P {ω | ω ∈ H ∧ (R ω, F ω) ∈ D} =
      P H * P {ω | (R ω, F ω) ∈ D} := by sorry
