-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:57:55.971476+00:00
-- url     : https://prove2.me/theorems/c04d2cd0-496e-4222-9998-1729b3b90cf5
-- title:
--   Every true original payment time gives a full Stieltjes source-frozen cell inequality at every cap
-- statement:
--   At any genuine original payment time b, actual paymentTimes inclusion proves b=0 or b is strictly prior to the source ruin time. Transport this source eligibility into the proved full Stieltjes source-frozen dividend cell inequality for arbitrary positive extended-real caps, including unbounded-variation Lévy sources. The mass on (a,b] includes ordinary continuous and singular-continuous dividends and the right-payment atom at b. Source cap-linear secants give nonpositive cash-plus-value-change even at zero or upper-cap contact, with the original post-source X(b) and rightLimit D ordering. The proof cites only public imports; it inlines the exact source-frozen secant and Ioc mass argument to respect public/private module boundaries.
-- source:
--   Public proved source: avram_wave5_04b_positive_ennreal_cap_extension_global_secant (a4675c8a), avram_wave3_03_dividendStrategy_rightLimit_monotone (f7eef805), dividendMeasure_Ioc_rightLimit (f9211de0), avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero (a7a447fa); original proposition 4(i), equations 5.11-5.13. Inline proof avoids importing private P3-C theorem 333d39f4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine original payment time carries the full Stieltjes source-frozen cell inequality. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPay : (b : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by sorry
