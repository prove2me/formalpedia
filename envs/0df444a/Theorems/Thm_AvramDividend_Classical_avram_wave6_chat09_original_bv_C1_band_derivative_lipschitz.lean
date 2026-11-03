-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:17:14.185335+00:00
-- url     : https://prove2.me/theorems/82f28985-8487-48dd-8fe3-62e55e03aff1
-- title:
--   Original-source BV C¹ compact reserve-band derivative envelope yields exact local Lipschitz secants
-- statement:
--   For the genuine spectrally negative Lévy source in the bounded-variation branch and a canonical C¹ function on its strictly positive finite-cap interior, an explicitly bounded derivative on a closed reserve strip implies the real absolute-value Lipschitz estimate needed by the accepted original pre/postpayment mesh theorem. The strip is contained in the open C¹ interior; no global monotonicity or Lipschitzness of w is imposed. This isolates the derivative-envelope to local-payment-clock bridge and retains the original source objects.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), C1 bounded-variation verification; compact reserve-strip mean-value estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ (K : ℝ) * |s - t| := by sorry
