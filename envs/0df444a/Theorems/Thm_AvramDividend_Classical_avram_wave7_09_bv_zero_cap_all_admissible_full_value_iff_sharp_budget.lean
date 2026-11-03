-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_all_admissible_full_value_iff_sharp_budget
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_full_value_iff_sharp_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:43:18.298146+00:00
-- url     : https://prove2.me/theorems/5c1455ce-6864-4162-94c5-d5b1e6c55985
-- title:
--   Exact BV zero-cap full dividendValue budget uniformly for all admissible strategies
-- statement:
--   For every genuine finite-activity standing BV spectrally negative Lévy source X, the exact threshold for a bound A on the original full discounted Stieltjes dividendValue of every cap-zero admissible D from initial reserve zero is the first-jump reflected value ENNReal.ofReal(drift/(q+nu(Iio0).toReal)). The necessity witness is the original barrierStrategy X 0 0, Proved admissible by 32b4ccb8. Sufficiency is the Proved original all-zero-cap strategy comparison 570b5248. The Proved exact reflected value formula 6f73f927 and identity 11b589b7 compute the sharp threshold. Unlike the finite-horizon branch, this statement directly applies to full dividendValue consumers.
-- source:
--   Genuine original sample space, X/P/filtration, D and original dividendValue; no Open import or substituted process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_full_value_iff_sharp_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      dividendValue X q 0 D ≤ A) ↔
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤ A  := by sorry
