-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_image_finite_carrier
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_image_finite_carrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:34:20.982954+00:00
-- url     : https://prove2.me/theorems/1e6d0da8-bf42-494e-b3a3-b9440513764c
-- title:
--   Finite carrier for a finite-mass compactified original image measure
-- statement:
--   A real Borel measure of finite total mass that is almost everywhere carried by [0,1] has an equal finite-measure representation whose complement-of-unit-interval mass is zero. This forms the concrete coercion interface between the original Lévy weighted image measure and the weak topology of finite measures.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_image_finite_carrier (μ : Measure ℝ)
    (hmass : μ Set.univ < ⊤)
    (hunit : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ρ : FiniteMeasure ℝ,
      (ρ : Measure ℝ) = μ ∧ ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by sorry
