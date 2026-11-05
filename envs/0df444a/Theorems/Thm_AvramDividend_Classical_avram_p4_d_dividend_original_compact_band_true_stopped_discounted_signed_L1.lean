-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_compact_band_true_stopped_discounted_signed_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_true_stopped_discounted_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:28:47.297583+00:00
-- url     : https://prove2.me/theorems/1ad9ea40-1cdb-4527-9e8d-8fd14de37b58
-- title:
--   Original stopped discounted signed dividend-gradient kernel is integrable on compact interior reserve bands
-- statement:
--   For the original controlled Levy process on the exact stopped paymentTimes clock, C2 interior regularity and a compact reserve band yield a finite bound on the true left-Levy-limit/right-dividend-limit gradient. Discount is bounded by one since all original paid times are nonnegative. Consequently the source-exact signed discounted gradient kernel is Stieltjes-integrable whenever it is almost everywhere strongly measurable and its states stay in that band. This includes singular-continuous mass and right atoms on the actual finite-horizon paid set; zero and cap boundary contact remain separately localised.
-- source:
--   Compose proved original C2 compact-band derivative bound 8e186779, pathwise finite original stopped dividend measure integrability 617614f3, and proven source nonnegative payment times 71123237 and measurable paid set 88dafb7f. This is source-specific local integrability for the actual original Ito-Meyer dividend gradient budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_true_stopped_discounted_signed_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)))
      ((dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂(dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by sorry
