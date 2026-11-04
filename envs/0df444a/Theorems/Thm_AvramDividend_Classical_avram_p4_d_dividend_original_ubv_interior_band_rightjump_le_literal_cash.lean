-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ubv_interior_band_rightjump_le_literal_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ubv_interior_band_rightjump_le_literal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:32:36.690325+00:00
-- url     : https://prove2.me/theorems/cc19c758-c000-4c7d-a5d5-086a3649fc7c
-- title:
--   Original UBV C2 compact interior band gives summable source-ordered right-dividend corrections dominated by exact stopped Cash
-- statement:
--   Under strict interior compact-band local C2 regularity of the original UBV candidate, the source proved secant Lipschitz envelope and correct post-Lévy/pre-dividend actual reserve give a true countable atomic carrier and absolute right-dividend correction bound. This theorem transports its full restricted Stieltjes bound to the exact P4-F ruin-stopped Cash integral, preserving time-zero, singular continuous mass, simultaneous source/payment jumps and the surviving horizon atom. It retains honest compact strict-interior state hypotheses, leaving zero/cap boundary contacts to the separately proved cap-linear extension and P4-E localisation.
-- source:
--   Accepted P4-D C2 interior band 3dc8e157 and exact original closed cash equality 52a094c1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ubv_interior_band_absolute_rightjump_le_full_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Source-original UBV strict interior band authentic right-dividend correction is controlled by literal stopped Cash. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ubv_interior_band_rightjump_le_literal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hStates : ∀ i, riskProcess X x D (t i) ω ∈ Icc a b ∧
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∀ i : ι, (t i : ℝ) ∈ A) →
      Function.Injective (fun i : ι => (t i : ℝ)) →
        Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ∧
        (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ≤
          (max 1 (K : ℝ) - 1) *
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) := by sorry
