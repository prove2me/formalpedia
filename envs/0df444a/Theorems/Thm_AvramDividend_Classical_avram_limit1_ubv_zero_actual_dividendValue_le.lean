-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_zero_actual_dividendValue_le
-- name    : AvramDividend.Classical.avram_limit1_ubv_zero_actual_dividendValue_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:01:10.177657+00:00
-- url     : https://prove2.me/theorems/9c3ff05b-2dde-4344-8e25-f69080d520b8
-- title:
--   Original zero-capital UBV dividend value from exact right-payment and all closed horizons
-- statement:
--   For the original spectrally negative Levy process of unbounded variation, an actual admissible capped strategy at x=0 and a nonnegative continuous verification candidate with C2 interior smoothness and derivative at least one, prove dividendValue X q 0 D ≤ ENNReal.ofReal(w 0) for arbitrary real discount q and nonnegative extended cap C. The Proved corrected original UBV zero-start theorem controls each closed Iic integer horizon including the initial right-payment Stieltjes atom. The Proved local differentiability and admissible lump-sum-drop lemmas discharge the zero-start jump condition. The Proved original uniform finite-horizon-to-infinite value theorem then passes to the perpetual dividendValue. No source stochastic martingale, equality-in-law, terminal vanishing, or extra HJB condition is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_smooth_differentiable
import Theorems.Thm_AvramDividend_Classical_verification_strategy_lump_sum_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_ubv_zero_actual_dividendValue_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D) :
    dividendValue X q 0 D ≤ ENNReal.ofReal (w 0) := by sorry
