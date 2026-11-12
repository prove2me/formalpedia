-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_joint_law_of_right_ray_rectangles
-- name    : AvramDividend.Classical.avram_a06_generic_joint_law_of_right_ray_rectangles
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-11T08:17:52.471582+00:00
-- url     : https://prove2.me/theorems/e28e1ac9-c660-4c80-ab2a-62bcea9194b1
-- title:
--   Joint distributions of nonnegative residuals and full future streams are determined by right-ray rectangles
-- statement:
--   For two almost-everywhere measurable joint random variables consisting of a nonnegative real residual and an infinite real stream, equality of all probabilities of right-ray times arbitrary Borel tail-stream sets implies equality of their complete joint laws.
-- source:
--   Use extension from the π-system of right half-lines on ℝ≥0 crossed with arbitrary measurable tail-stream sets. Nonnegative residual assumptions reduce negative thresholds to universals; measure uniqueness on rectangles then yields equality of product-space pushforward probability measures.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_joint_law_of_right_ray_rectangles
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R U : Ω → ℝ) (F G : Ω → (ℕ → ℝ))
    (hRF : AEMeasurable (fun ω => (R ω, F ω)) P)
    (hUG : AEMeasurable (fun ω => (U ω, G ω)) P)
    (hRpos : ∀ᵐ ω ∂P, 0 ≤ R ω)
    (hUpos : ∀ᵐ ω ∂P, 0 ≤ U ω)
    (hrect : ∀ (t : ℝ), 0 ≤ t →
      ∀ (B : Set (ℕ → ℝ)), MeasurableSet B →
      P {ω | t < R ω ∧ F ω ∈ B} =
      P {ω | t < U ω ∧ G ω ∈ B}) :
    IdentDistrib (fun ω => (R ω, F ω)) (fun ω => (U ω, G ω)) P P := by sorry
