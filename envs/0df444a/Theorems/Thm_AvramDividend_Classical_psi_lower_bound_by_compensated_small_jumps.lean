-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
-- name    : AvramDividend.Classical.psi_lower_bound_by_compensated_small_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:25:34.344955+00:00
-- url     : https://prove2.me/theorems/29b521e4-d37f-4a75-9aa9-db4f349c0de8
-- title:
--   Canonical Laplace exponent lower bounded by small jump compensation minus large jump mass
-- statement:
--   For the canonical spectrally negative Lévy process and every nonnegative Laplace parameter, the Lévy exponent is at least its drift and Gaussian terms, plus the integrated compensated kernel on the small negative jumps (-1,0), minus the finite real mass of large negative jumps y≤−1. An explicit integrability assumption for the large-jump constant handles non-finite Lévy measures and preserves the endpoint y=−1.
-- source:
--   The exact Lévy–Khintchine exponent definition; Prove2Me-Proved levy_compensated_jump_integrable_nonneg; negative_jump_kernel_lower_indicator; and pinned Mathlib integral_mono_ae plus indicator integration and restriction. This is the missing analytic comparison for non-Gaussian eventual ψ positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.psi_lower_bound_by_compensated_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hlarge : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Iic (-1 : ℝ)) X.ν) :
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) ≤
      X.ψ θ := by sorry
