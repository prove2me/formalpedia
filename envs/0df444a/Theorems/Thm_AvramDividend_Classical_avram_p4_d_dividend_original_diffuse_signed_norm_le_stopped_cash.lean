-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_diffuse_signed_norm_le_stopped_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_diffuse_signed_norm_le_stopped_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:39:58.057207+00:00
-- url     : https://prove2.me/theorems/bc3d862a-992b-4217-b215-2d73a0db9af6
-- title:
--   Original stopped signed diffuse dividend correction bounded by true discounted Cash
-- statement:
--   On the actual original controlled Lévy reserve, for any Stieltjes dividend submeasure dominated by dividendMeasure with its pre-dividend source reserve in a compact strict-interior band almost everywhere, there exists a nonnegative finite band-dependent K bounding the absolute signed dividend gradient Stieltjes correction by (1+K) times true original finite-horizon discounted stopped Cash.toReal divided by exp(-qT). This includes absolutely continuous and singular-continuous components and preserves the actual closed paid clock, without claiming boundary contact is covered by derivative assumptions.
-- source:
--   Accepted exact original signed gradient norm bound ff7facab plus actual stopped Cash real-mass bound on the same paymentTimes/closed horizon; multiplication monotonicity in real numbers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_norm_le_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_diffuse_signed_norm_le_stopped_cash
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
        (1 + K) *
          ((∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
             Real.exp (-(q * (T : ℝ)))) := by sorry
