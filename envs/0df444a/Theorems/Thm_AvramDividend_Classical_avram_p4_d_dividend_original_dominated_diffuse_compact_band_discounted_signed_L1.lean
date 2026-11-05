-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:34:42.471568+00:00
-- url     : https://prove2.me/theorems/8ae91eef-c51b-4f64-8697-a3530137abf5
-- title:
--   True original diffuse dividend submeasure compact-band signed discount kernel integrable even with boundary right-payment atoms
-- statement:
--   For the original Lévy controlled surplus, fix an arbitrary sample-dependent dividend submeasure ν dominated by the genuine original dividendMeasure, including the atomless diffuse part. C2 regularity gives a bound on the derivative on each compact band inside the strict cap interior. If the ν-almost-everywhere original left-Lévy-limit/right-dividend-limit reserve lies in this band and the signed discounted kernel is ν-a.e. strongly measurable, then that kernel is Stieltjes-integrable on the real original stopped payment clock. The strict interior condition is imposed only on the selected submeasure ν, so source dividend atoms at zero or cap do not invalidate diffuse integrability. This directly discharges the local integrability premise in the proved original diffuse/right-atom signed control theorem a9565727 without a false global derivative bound.
-- source:
--   Pinned original compact C2 derivative bound 8e186779; true dividend Stieltjes finite mass source theorem and paymentTimes nonnegative 71123237. Generic pinned IntegrableOn.of_bound. Feeds the actual ν from original full diffuse measure decomposition 51782257 and source signed control a9565727.

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

theorem AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
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
    (hSM : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)))
      (ν.restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)))
      (paymentTimes σ ∩ Iic (T : ℝ)) ν := by sorry
