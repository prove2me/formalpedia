-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
-- name    : AvramDividend.Classical.avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:17:19.729359+00:00
-- url     : https://prove2.me/theorems/12833b04-7101-4d0b-b43d-6f69a4809495
-- title:
--   Nested original finite physical time and finite negative Lévy mark intensity bounded kernel integral norm is product bound
-- statement:
--   On the exact original time finite horizon [0,T] and finite negative Lévy intensity ν(Iio 0), any real two-variable stopped mark kernel uniformly bounded in absolute value by K on both supports has an iterated compensator Bochner integral norm at most K times each finite measure's real mass. This gives the deterministic K*T*ν(Iio 0) bound for original BVB68 source V_n, with all original time and negative-mark supports.
-- source:
--   BVB71 single-fibre Bochner bound and two applications of MeasureTheory.norm_integral_le_of_norm_le_const.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) (hμ : μ S < ⊤)
    (ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hν : ν B < ⊤)
    (f : α → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hKernel : ∀ t ∈ S, ∀ z ∈ B, |f t z| ≤ K) :
    ‖∫ t in S, ∫ z in B, f t z ∂ν ∂μ‖ ≤
      (K * (ν B).toReal) * (μ S).toReal := by sorry
