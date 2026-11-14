-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb74_finite_double_integral_uniform_kernel_norm_bound
-- name    : AvramDividend.Classical.avram_bvb74_finite_double_integral_uniform_kernel_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T18:01:36.918455+00:00
-- url     : https://prove2.me/theorems/b20d7169-dd9b-4974-b371-83e0528dcefc
-- title:
--   Uniformly bounded real kernel integrated twice against finite physical and negative mark measures has explicit product-mass norm bound
-- statement:
--   Given two finite source measures and a real-valued kernel H_n that is pointwise uniformly bounded in absolute value by K, prove that the norm of its iterated real Bochner integral is at most K times the real masses of the two finite measures. This is the exact abstract two-step Bochner norm bound needed in original BV finite negative-jump predictable-mark source BVB72. It does not require any speculative Markov or stochastic compensation assumptions.
-- source:
--   Pinned Mathlib MeasureTheory.norm_integral_le_of_norm_le_const twice; source BVB72 exact strict physical predictable time measure and finite negative Lévy mark measure.

import Mathlib
open Classical MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bvb74_finite_double_integral_uniform_kernel_norm_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℕ → α → β → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hBound : ∀ n a b, |H n a b| ≤ K) :
    ∀ n : ℕ,
      ‖∫ a, ∫ b, H n a b ∂ν ∂μ‖ ≤
        (K * ν.real Set.univ) * μ.real Set.univ := by sorry
