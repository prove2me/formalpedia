-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys54_supported_integral_norm_le_count
-- name    : AvramDividend.Classical.avram_bvb_phys54_supported_integral_norm_le_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:42:59.384258+00:00
-- url     : https://prove2.me/theorems/aa4ba04d-780d-490b-b0ca-a70eaee8abc6
-- title:
--   Bound the integral of a bounded supported reward by support measure
-- statement:
--   An integrable real reward supported on a measurable set of finite measure and uniformly bounded there by K has integral norm at most K times the set's measure.
-- source:
--   Measure-theoretic step of original finite-activity fullmask count-domination: combine Proved compact-cap reward kernel bound cf0d73ae with almost surely finite negative jump count 1d9db509, then apply this supported-integral estimate.

import Mathlib
open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys54_supported_integral_norm_le_count
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hSm : MeasurableSet S) (hFinite : μ S < ⊤)
    (f : α → ℝ) (hf : Integrable f μ)
    (hSupport : ∀ a, a ∉ S → f a = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ a ∈ S, ‖f a‖ ≤ K) :
    ‖∫ a, f a ∂μ‖ ≤ K * (μ S).toReal := by sorry
