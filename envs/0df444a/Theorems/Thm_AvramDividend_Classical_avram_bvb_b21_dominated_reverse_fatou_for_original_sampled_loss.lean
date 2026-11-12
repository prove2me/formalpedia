-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_dominated_reverse_fatou_for_original_sampled_loss
-- name    : AvramDividend.Classical.avram_bvb_b21_dominated_reverse_fatou_for_original_sampled_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:41:14.833773+00:00
-- url     : https://prove2.me/theorems/1578a04d-6766-41e0-aad5-0fd19ed3ece7
-- title:
--   Dominated reverse Fatou for one-sided original sampled mark loss
-- statement:
--   For nonnegative original-grid sampled loss kernels dominated by a single integrable kernel, an almost-everywhere one-sided pointwise limsup bound controls the limsup of their integrals. No contact-occupation sampling assumption is required.
-- source:
--   Necessary measure-theoretic integral bridge for original BV phys95 and the later-ruin quadrature; finite-cap domination and contact-safe pointwise bounds are separate obligations.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_dominated_reverse_fatou_for_original_sampled_loss
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ≥0∞) (g h : α → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hbound : ∀ n, f n ≤ᵐ[μ] g)
    (hfinite : (∫⁻ t, g t ∂μ) ≠ ⊤)
    (hpoint : ∀ᵐ t ∂μ,
      Filter.limsup (fun n : ℕ => f n t) Filter.atTop ≤ h t) :
    Filter.limsup (fun n : ℕ => ∫⁻ t, f n t ∂μ) Filter.atTop ≤
      ∫⁻ t, h t ∂μ := by sorry
