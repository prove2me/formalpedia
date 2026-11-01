-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_product_square_kernel_integrable_of_domination
-- name    : AvramDividend.Classical.avram_wave4_p1_marked_product_square_kernel_integrable_of_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:13:11.991754+00:00
-- url     : https://prove2.me/theorems/04a3e4f3-0b05-42c8-b895-44966f88eb2b
-- title:
--   Finite-time marked compensator quadratic integrability under a finite Lévy square-energy envelope
-- statement:
--   If the time/sample base has finite measure and a nonnegative mark energy g is ν-integrable, any (possibly state-dependent) nonnegative marked square-kernel F bounded pointwise by a finite constant times g(mark) is integrable under the genuine product intensity μ⊗ν. The result holds with ν of infinite activity and uses the one-sided Tonelli inequality; no stochastic compensation or martingale identity is assumed. Apply with F=|reserve-dependent stopped jump remainder|² and g(z)=|z|² on small-jump bands.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_prod_le, lintegral_const_mul and lintegral_const; Applebaum Lévy stochastic integration and Avram-Palmowski-Pistorius (2007), Proposition 4(i).

import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_marked_product_square_kernel_integrable_of_domination
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (F : A × E → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : C < ∞)
    (hdom : ∀ p, F p ≤ C * g p.2) :
    ∫⁻ p, F p ∂μ.prod ν < ∞ := by sorry
