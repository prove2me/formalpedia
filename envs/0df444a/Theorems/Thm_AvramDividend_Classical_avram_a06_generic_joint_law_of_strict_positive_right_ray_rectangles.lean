-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_joint_law_of_strict_positive_right_ray_rectangles
-- name    : AvramDividend.Classical.avram_a06_generic_joint_law_of_strict_positive_right_ray_rectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:20:08.728663+00:00
-- url     : https://prove2.me/theorems/c5031deb-fd03-4e8d-ad78-8c6ffc3ae843
-- title:
--   Strictly positive residual and future-stream joint laws are determined by right-ray rectangles
-- statement:
--   For two almost-everywhere measurable pairs of strictly positive residuals and infinite future streams, agreement on all right-ray times Borel-tail rectangles identifies their full joint distributions. Strict positivity prevents missing the residual-zero atom.
-- source:
--   Use the π-system of right half-lines on positive reals; derive the marginal tail-set probabilities from the t=0 case, extend to all real thresholds, and use Measure.ext_of_Iic followed by Measure.ext_prod for the joint pushforwards. Positive residuals are required.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_joint_law_of_strict_positive_right_ray_rectangles
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R U : Ω → ℝ) (F G : Ω → (ℕ → ℝ))
    (hRF : AEMeasurable (fun ω => (R ω, F ω)) P)
    (hUG : AEMeasurable (fun ω => (U ω, G ω)) P)
    (hRpos : ∀ᵐ ω ∂P, 0 < R ω)
    (hUpos : ∀ᵐ ω ∂P, 0 < U ω)
    (hrect : ∀ (t : ℝ), 0 ≤ t →
      ∀ (B : Set (ℕ → ℝ)), MeasurableSet B →
      P {ω | t < R ω ∧ F ω ∈ B} =
      P {ω | t < U ω ∧ G ω ∈ B}) :
    IdentDistrib (fun ω => (R ω, F ω)) (fun ω => (U ω, G ω)) P P := by sorry
