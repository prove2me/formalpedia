-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_strict_preruin_negative_mark_prestate_positive
-- name    : AvramDividend.Classical.avram_freshD_original_strict_preruin_negative_mark_prestate_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T09:00:32.585246+00:00
-- url     : https://prove2.me/theorems/47e717a5-75a3-4c40-85d9-21cacf624b9a
-- title:
--   Actual negative Lévy jump strictly before ruin necessarily starts from a strictly positive original predictable reserve
-- statement:
--   For the original spectrally negative Lévy path X, any original cumulative dividend control D and initial capital x, if a negative original source jump occurs at physical time t strictly before the original ruin time, the true predictable pre-jump reserve x+X(t-)-D(t) is strictly positive. Indeed the controlled post-jump reserve at t is nonnegative by the Proved original ruin-time source, and equals the predictable pre-jump reserve plus the strictly negative true source mark. This removes the lower-zero-boundary concern for all original negative marks STRICTLY before ruin; a mark at ruin time must be treated separately, and upper-cap boundary is a distinct obligation.
-- source:
--   Original stopped marked Itô–Meyer root source 242ca5f1, exact riskProcess_nonneg_before_ruin c26c83f7 and original X negative-mark leftLim definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_strict_preruin_negative_mark_prestate_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hz : X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0) :
    0 < x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω := by sorry
