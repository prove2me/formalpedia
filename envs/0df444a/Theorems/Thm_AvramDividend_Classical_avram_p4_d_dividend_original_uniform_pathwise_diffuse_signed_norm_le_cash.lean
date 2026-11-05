-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_uniform_pathwise_diffuse_signed_norm_le_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_uniform_pathwise_diffuse_signed_norm_le_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:41:21.243111+00:00
-- url     : https://prove2.me/theorems/fdff6621-b8c8-45d4-a1c5-d5aecdaa1c10
-- title:
--   One deterministic compact-band coefficient bounds every original stopped diffuse dividend remainder by Cash
-- statement:
--   For the original Lévy source and an admissible right-continuous dividend control, assume a fixed strict-interior compact band contains the left-X/right-D source reserve for νω-almost every stopped dividend time on all paths, with νω dominated by original dividendMeasure D ω. The source interior C2 hypothesis gives a single deterministic K≥0, independent of ω, such that the actual stopped signed discounted dividend-gradient correction has norm bounded pathwise by (1+K) times original paid Cash.toReal divided by the finite-horizon discount exp(-qT). This is the uniform pathwise envelope needed for expectation-level L1 after separately establishing measurability and an a.e. band localisation.
-- source:
--   Accepted source UBV C2 derivative bound 8e186779; uniform kernel helper on literal X leftLim/D rightLimit, true rightLimit Stieltjes finite mass and accepted real stopped Cash mass 159d8858. Deterministic K does not vary with ω.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_uniform_pathwise_diffuse_signed_norm_le_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ν : Ω → Measure ℝ)
    (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      ‖∫ s in (paymentTimes σ ∩ Iic (T : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(ν ω)‖ ≤
        (1 + K) *
          ((∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
              Real.exp (-(q * (T : ℝ)))) := by sorry
