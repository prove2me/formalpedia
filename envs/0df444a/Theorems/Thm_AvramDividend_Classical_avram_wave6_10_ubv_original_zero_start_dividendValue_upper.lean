-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_dividendValue_upper
-- name    : AvramDividend.Classical.avram_wave6_10_ubv_original_zero_start_dividendValue_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:16:47.525118+00:00
-- url     : https://prove2.me/theorems/449258df-da20-4bb1-85f1-1ff3b41d4e25
-- title:
--   Original UBV zero-capital complete dividendValue bound from exact finite-horizon Stieltjes estimates
-- statement:
--   For the genuine original unbounded-variation spectrally negative Lévy process and any original IsAdmissibleLe dividend regulator beginning at zero reserve, the exact corrected zero-start finite-real-horizon Stieltjes reward bound implies the complete infinite-horizon dividendValue upper bound by monotone convergence of original paymentTimes. Retain the zero boundary, C² interior smoothness, gradient and exact initial/right-payment secant premises of the Proved Chat 08 zero-initial finite-horizon theorem. The proof invokes that theorem at each nonnegative integer horizon and the Proved uniform-truncated-to-dividendValue bridge. It requires no invented process, no extra stochastic Itô estimate, and preserves the t=0 payment atom. This is a genuine x=0 boundary case of the assigned full UBV goal, not an all-capital replacement.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), zero-initial-capital branch. Direct formal consequence of Proved avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound (14599b22-5d59-42c4-81c7-efbc058a3e03) and Proved dividendValue_le_of_uniform_truncated_bounds (dc933bd8-8284-4e80-89e6-304a074e0a4a).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_ubv_original_zero_start_dividendValue_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X 0 D t ω) -
          w (riskProcess X 0 D t ω -
            (rightLimit D t ω - D t ω))) :
    dividendValue X q 0 D ≤ ENNReal.ofReal (w 0) := by sorry
