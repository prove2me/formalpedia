-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess18_original_zero_contact_nojump_cash_le_HJB_envelope
-- name    : AvramDividend.Classical.avram_bv_excess18_original_zero_contact_nojump_cash_le_HJB_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:44:49.254505+00:00
-- url     : https://prove2.me/theorems/ee13144f-dd04-4520-bf6a-caa49f834d8a
-- title:
--   Original finite-activity zero-reserve no-jump cash bounded by the origin HJB envelope
-- statement:
--   For the actual original spectrally negative BV process, any genuine no-claim cell that starts at zero post-payment reserve and ends at nonnegative post-payment reserve pays at most X.drift times the cell width. The already proved origin HJB drift ceiling replaces this drift by (q+nu negative total)*w(0), giving a source-exact bound that compensates the missing zero-contact jump loss in the 233260f7 finite-activity physical ledger. No arbitrary-grid convergence is claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess18_original_zero_contact_nojump_cash_le_HJB_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hzeroa : riskProcess X x D a ω -
      (rightLimit D a ω - D a ω) = 0)
    (hpositiveb : 0 ≤ riskProcess X x D b ω -
      (rightLimit D b ω - D b ω))
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal
        (((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
          ((b : ℝ) - (a : ℝ))) := by sorry
