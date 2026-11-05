-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:46:25.501261+00:00
-- url     : https://prove2.me/theorems/16541009-23f3-42cd-bd53-d452c6f6b8e1
-- title:
--   Original stopped diffuse dividend signed budget nonpositive from local C2 compact-band integrability
-- statement:
--   On the exact finite stopped payment set of an original Lévy-controlled dividend process, let ν be an atomless sample-dependent submeasure of the genuine dividend Stieltjes measure. If the ν-almost-everywhere original left-Levy-limit/right-dividend-limit reserve lies in a compact strict-interior band, the smooth payoff derivative is at least one there, the discount is nonincreasing, and the true kernel is ν-almost-everywhere strongly measurable, then its signed discounted diffuse Stieltjes integral is well-defined and nonpositive. This removes the integrability hypothesis in the already proved source-exact diffuse sign theorem. It includes singular-continuous payments, while cap/zero right atoms, including at time zero, ruin and horizon, are handled by their separately proved jump secant contribution.
-- source:
--   Direct source-exact corollary of accepted P4-D compact submeasure signed L1 theorem 8ae91eef and accepted P4-D original selected diffuse signed integral sign theorem fa6f235f. Original paymentTimes and Stieltjes measure definitions preserved; ν is the genuine diffuse witness from 51782257 when available.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
        s.toNNReal - rightLimit D s.toNNReal ω)))
      (ν.restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω ∈ Icc a b) :
    (∫ s in (paymentTimes σ ∩ Iic (T : ℝ)), Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
        s.toNNReal - rightLimit D s.toNNReal ω)) ∂ν) ≤ 0 := by sorry
