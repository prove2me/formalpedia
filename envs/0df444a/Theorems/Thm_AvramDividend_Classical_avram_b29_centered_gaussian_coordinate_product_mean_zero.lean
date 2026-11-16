-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_centered_gaussian_coordinate_product_mean_zero
-- name    : AvramDividend.Classical.avram_b29_centered_gaussian_coordinate_product_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:03:24.990215+00:00
-- url     : https://prove2.me/theorems/d835f03e-db62-45a5-99db-032822b0a38b
-- title:
--   Centred integrable Brownian-only physical mesh gains remain centred and integrable under independent Brownian–Poisson product probability
-- statement:
--   For each Brownian-coordinate physical mesh gain H_k integrable and centred on its own probability space μ, lift the gain to the product μ.prod ν with an independent Poisson input ν by pullback of the first projection. Integrability is preserved by Mathlib Integrable.comp_fst, and the product expectation equals ν.real(univ) times the Brownian expectation by Mathlib integral_fun_fst, hence zero for every k. This discharges the exact product-integrability and product-zero-mean premises in the B25/B29 no-large-jump event centring route without assuming them directly on product space.
-- source:
--   Mathlib.MeasureTheory.Integral.Prod integral_fun_fst and Integrable.comp_fst; B25/B29 independent Brownian–Poisson original mesh obstruction, 15 November 2026

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_b29_centered_gaussian_coordinate_product_mean_zero
    {ΩB ΩN : Type*} [mB : MeasurableSpace ΩB]
    [mN : MeasurableSpace ΩN]
    (μ : Measure ΩB) (ν : Measure ΩN)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : ℕ → ΩB → ℝ)
    (hIntegrable : ∀ k, Integrable (H k) μ)
    (hMean : ∀ k, (∫ ω, H k ω ∂μ) = 0) :
    (∀ k, Integrable (fun p : ΩB × ΩN => H k p.1) (μ.prod ν)) ∧
    (∀ k, (∫ p : ΩB × ΩN, H k p.1 ∂(μ.prod ν)) = 0) := by sorry
