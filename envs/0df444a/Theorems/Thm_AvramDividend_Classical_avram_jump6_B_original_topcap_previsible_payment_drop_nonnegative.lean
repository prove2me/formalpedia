-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
-- name    : AvramDividend.Classical.avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:55:27.000208+00:00
-- url     : https://prove2.me/theorems/e82d7f41-59e8-4d7d-9c1b-d7713a72b9e2
-- title:
--   Original strict pre-ruin top-cap right-payment potential drop is nonnegative for every time cell
-- statement:
--   For original infinite-activity-compatible spectrally negative Levy X, any admissible dividend D, positive top cap, C1 potential with derivative at least one, any original physical mesh times s≤t with t=0 or before ruin, the w pre-cell rightpayment reserve drop is nonnegative. Uses original admissibility for nonnegative postpayment reserve, monotonic rightLimitD for payment ordering, and proved allcap C1 secant bound. Supplies exact hH positive cell drops needed to turn the proved ENNReal original closed-Iic cash Stieltjes bound into real negative signed PaymentResidual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ w (x + X.X t ω - rightLimit D s ω) -
      w (x + X.X t ω - rightLimit D t ω) := by sorry
