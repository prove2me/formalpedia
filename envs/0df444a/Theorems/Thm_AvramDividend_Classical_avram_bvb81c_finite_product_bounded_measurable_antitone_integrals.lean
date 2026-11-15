-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb81c_finite_product_bounded_measurable_antitone_integrals
-- name    : AvramDividend.Classical.avram_bvb81c_finite_product_bounded_measurable_antitone_integrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:21:22.772089+00:00
-- url     : https://prove2.me/theorems/8d858ef7-1494-434f-b42f-88634ea1637e
-- title:
--   Bounded measurable antitone kernels have antitone iterated integrals over finite measures
-- statement:
--   On two finite measure spaces, a uniformly bounded jointly measurable sequence of real kernels decreasing pointwise has decreasing iterated Bochner integrals. Uniform bound supplies integrability of each inner and outer section, so the nested integral comparison is valid. This corrected publication removes the unavailable Avram namespace opening from the generic Mathlib-only preamble; the original request failed compilation under autoImplicit=false.

import Mathlib
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb81c_finite_product_bounded_measurable_antitone_integrals
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (ν : Measure β) [IsFiniteMeasure ν]
    (f : ℕ → α → β → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hMeas : ∀ n : ℕ, Measurable (Function.uncurry (f n)))
    (hBound : ∀ n a b, ‖f n a b‖ ≤ K)
    (hAntitone : ∀ n m : ℕ, n ≤ m → ∀ a b, f m a b ≤ f n a b) :
    Antitone (fun n : ℕ => ∫ a, ∫ b, f n a b ∂ν ∂μ) := by sorry
