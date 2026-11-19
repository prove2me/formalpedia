-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_initial_caplinear_postvalue_budget
-- name    : AvramDividend.Classical.avram_jump6_B_original_anycap_initial_caplinear_postvalue_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:15:11.393194+00:00
-- url     : https://prove2.me/theorems/3ee8ba28-4aee-4360-aecb-7bbb1367a808
-- title:
--   True original all-cap initial right payment plus caplinear postpayment potential is bounded by initial potential
-- statement:
--   For the original Levy X, any positive finite or infinite dividend cap C, any admissible dividend D and cap-linear extension V of the genuine HJB candidate w, the time-zero right dividend plus postpayment V(x-rightLimitD0) is bounded by V(x). Original nonnegative reserve after the initial rightpayment, D(0)=0, and the existing Proved all-cap global gradient secant imply this. This establishes the exact true initial atom sign used in the finite-cap canonical physical Stieltjes cash ledger without finite-activity assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anycap_initial_caplinear_postvalue_budget
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
    (ω : Ω) :
    rightLimit D 0 ω + V (x - rightLimit D 0 ω) - V x ≤ 0 := by sorry
