-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_previsible_caplinear_payment_drop_nonnegative
-- name    : AvramDividend.Classical.avram_jump6_B_original_anycap_previsible_caplinear_payment_drop_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:14:39.903251+00:00
-- url     : https://prove2.me/theorems/8e96cba0-ac8d-42e7-b7e9-b2c723f09041
-- title:
--   True original all-cap previsible right-payment caplinear potential drop is nonnegative
-- statement:
--   For the original spectrally negative Levy X with any positive finite or infinite admissible dividend cap, a genuine physical previsible cell s≤t at time zero or strictly before ruin has nonnegative cap-linear extended potential drop V(Z)-V(Y). Obtained from original nonnegative postpayment reserve, monotone rightLimit D and proved global C1 lower-gradient secant for cap-linear extension V. Does not assume bounded variation or finite jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anycap_previsible_caplinear_payment_drop_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ V (x + X.X t ω - rightLimit D s ω) -
      V (x + X.X t ω - rightLimit D t ω) := by sorry
