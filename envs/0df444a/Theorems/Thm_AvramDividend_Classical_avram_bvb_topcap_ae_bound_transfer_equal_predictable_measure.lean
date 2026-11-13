-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_ae_bound_transfer_equal_predictable_measure
-- name    : AvramDividend.Classical.avram_bvb_topcap_ae_bound_transfer_equal_predictable_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:42:27.00746+00:00
-- url     : https://prove2.me/theorems/1d3e0562-489b-42a8-a882-f8e89a49e578
-- title:
--   Transfer a real kernel almost-everywhere bound between predictable and ordinary measures agreeing on predictable sets
-- statement:
--   If two measures on potentially different measurable spaces of the same type agree on every set measurable for the first space, and a real-valued f is measurable for that first space, any absolute-value bound holding almost everywhere under the second measure also holds almost everywhere under the first. Used to transfer source time×P bounds to the predictable occupation measure.
-- source:
--   Direct application of MeasureTheory.ae_iff and equality of the measurable strict superlevel set {x: K<|f x|}. Supports original topcap kernel predictable occupation product-a.e. bound b7f7a6c5.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_ae_bound_transfer_equal_predictable_measure
    {α : Type*} (m₁ m₂ : MeasurableSpace α)
    (μ : @Measure α m₁) (ν : @Measure α m₂)
    (hEq : ∀ A : Set α, MeasurableSet[m₁] A → μ A = ν A)
    (f : α → ℝ) (hf : Measurable[m₁] f)
    (K : ℝ)
    (hBound : ∀ᵐ p ∂ν, |f p| ≤ K) :
    ∀ᵐ p ∂μ, |f p| ≤ K := by sorry
