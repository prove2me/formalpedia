-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_postpayment_nonnegative_affine_terminal_floor
-- name    : AvramDividend.Classical.avram_wave8_ubv_original_postpayment_nonnegative_affine_terminal_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:20:49.794886+00:00
-- url     : https://prove2.me/theorems/5d3a0ca8-cb63-4ca8-b38d-16463990f0c9
-- title:
--   Original UBV postpayment zero-boundary affine terminal floor on nonnegative reserve
-- statement:
--   For the actual source spectrally negative Lévy X and admissible strategy D, if the observed postpayment reserve x+X_t-rightLimit D_t is nonnegative, the candidate value satisfies w(postpayment reserve)≥w(0)+postpayment reserve, uniformly for all caps including 0 and infinity. The only assumptions on w are the corrected core's positive-side continuity, interior C² and derivative ≥1. This follows from the Proved all-cap postpayment reserve bound and inclusive cap secant, and does not add any differentiability assumption at reserve zero or require bounded variation.
-- source:
--   Proved capped_postPaymentReserve_ofReal_le_cap and all-cap inclusive gradient secant 44b01929-5817-44ac-9439-6eb3c9879f2c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_ubv_original_postpayment_nonnegative_affine_terminal_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hy : 0 ≤ x + X.X t ω - rightLimit D t ω) :
    w 0 + (x + X.X t ω - rightLimit D t ω) ≤
      w (x + X.X t ω - rightLimit D t ω) := by sorry
