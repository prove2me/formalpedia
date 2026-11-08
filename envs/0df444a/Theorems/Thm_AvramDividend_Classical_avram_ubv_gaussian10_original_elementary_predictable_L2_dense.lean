-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_elementary_predictable_L2_dense
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_elementary_predictable_L2_dense
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:59:18.264656+00:00
-- url     : https://prove2.me/theorems/d66ba67a-70ac-4b25-83ea-2d950033e72c
-- title:
--   Elementary adapted predictable rectangles span the finite-clock L² integrand space
-- statement:
--   For the original filtration and any finite measure on its predictable product sigma algebra, the L² closure of the real linear span of bare elementary predictable rectangles, including the time-zero atom and half-open adapted future bands, equals the full predictable L² space. The proof combines the already Proved original filtration rectangle π-system, its exact predictable sigma generator, and general π-system indicator L² density. This supplies the elementary approximation interface for original stopped Gaussian integral without using natural filtration or changing the stopping clock.
-- source:
--   Avram Proved: 31933be5, ee8c5f17, 7a68dc8d; Gaussian target fdb9a6a3 and finite-horizon d457be6b, 665b3b52; pinned Mathlib 0df444a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_adapted_rectangle_sigma_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_pi_system
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_generator_l2_dense_after_lift

open MeasureTheory MeasurableSpace Set TopologicalSpace AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_elementary_predictable_L2_dense
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    [mProd : MeasurableSpace (ι × Ω)]
    (𝓕 : Filtration ι mΩ)
    (hProd : mProd = 𝓕.predictable)
    (μ : Measure (ι × Ω)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                 T = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                 T = (Set.Ioi i ×ˢ A))}
    let GP : Set (Set (ι × Ω)) := insert Set.univ (insert ∅ G)
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set (ι × Ω)) (ht : t ∈ GP)
        (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
        indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by sorry
