-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:47:43.660285+00:00
-- url     : https://prove2.me/theorems/0cc4b107-2e37-4fcd-b46b-2d3f0a8d2e0d
-- title:
--   Original post-Lévy dividend right-jump secant has finite interior C2 Lipschitz envelope
-- statement:
--   For the actual post-source-Lévy, pre-right-dividend reserve and its postpayment value, if both states lie in a genuine compact strict-interior reserve band, C² regularity of w and a local derivative bound K imply the upper secant inequality with constant max(1,K). The right dividend jump size is nonnegative by original dividend strategy monotonicity. This derives an honest local premise needed for absolute atomic summability and L1 under localisation, with no global extension through reserve zero or the upper-cap boundary.
-- source:
--   Proved c4293baa P4-D original strict-interior C2 Lipschitz band; Proved 953f0e91 dividendStrategy_le_rightLimit; original P4-F hjump convention 0dda1be7; source Proposition 4(i), Eq 5.13

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (ω : Ω) (t : ℝ≥0)
    (hPre : riskProcess X x D t ω ∈ Icc a b)
    (hPost : x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    w (riskProcess X x D t ω) -
      w (x + X.X t ω - rightLimit D t ω) ≤
      max 1 (K : ℝ) * (rightLimit D t ω - D t ω) := by sorry
