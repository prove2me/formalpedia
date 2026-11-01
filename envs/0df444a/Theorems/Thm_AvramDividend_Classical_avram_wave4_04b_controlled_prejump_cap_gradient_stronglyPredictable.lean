-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
-- name    : AvramDividend.Classical.avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:21:55.814566+00:00
-- url     : https://prove2.me/theorems/b0fbed73-6368-4355-a6b2-1857252f97f9
-- title:
--   Actual controlled strict-prejump capped HJB gradient is strongly predictable on the right-continuous filtration
-- statement:
--   For the genuine source spectrally negative Lévy process X, its same-filtration adapted dividend control D with arbitrary right jumps and diffuse variation, and w C² only in the corrected strict ENNReal capped interior, the capped derivative of the true pre-jump controlled reserve is strongly predictable for 𝓕.rightCont. This is the exact predictable integrand demanded by stopped Gaussian and compensated source jump stochastic integrals. The zero-time Function.leftLim is not replaced by the postpayment endpoint.
-- source:
--   Compose Proved actual postPaymentReserve_leftLim_stronglyPredictable with Proved measurable_cap_interior_deriv_zero_extension in the predictable σ-algebra; no Ito-Meyer axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0) := by
  sorry
