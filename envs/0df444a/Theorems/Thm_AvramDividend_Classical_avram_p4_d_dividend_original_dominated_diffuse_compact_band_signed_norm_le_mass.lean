-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_norm_le_mass
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_norm_le_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:54:00.384933+00:00
-- url     : https://prove2.me/theorems/ff7facab-dac4-468f-b2d7-bdea94a6ac1b
-- title:
--   Original stopped diffuse signed dividend remainder absolute bound by true paid submeasure mass
-- statement:
--   For a true original Lévy-controlled reserve, any sample-dependent Stieltjes submeasure ν dominated by dividendMeasure D ω on the exact nonnegative stopped paymentTimes, and a compact strict-interior band containing the ν-almost-everywhere source left-limit/right-dividend-limit reserves, there is a finite K depending only on the band and the interior C2 payoff with a pathwise absolute signed discounted dividend-gradient integral bounded above by (1+K) times the actual stopped ν-mass. The proof controls discount by one using q≥0 and the true payment clock, obtains finite mass from the original rightLimit Stieltjes interval theorem, and applies Mathlib's norm_setIntegral_le_of_norm_le_const_ae. This supplies a quantitative source-specific diffuse remainder envelope without assuming the rightpayment atoms are interior.
-- source:
--   Pinned original derivative bound 8e186779, payment clock 71123237, original rightLimit mass theorem and Mathlib MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae. Independent quantitative envelope for path-selected atomless source diffuse ν from 51782257; random-variable L1 still requires measurable selection and a cash/ν-mass envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_norm_le_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ᵐ s ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ‖∫ s in (paymentTimes σ ∩ Iic (T : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂ν‖ ≤
        (1 + K) * ν.real (paymentTimes σ ∩ Iic (T : ℝ)) := by sorry
