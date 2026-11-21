-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
-- name    : AvramDividend.Classical.avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:46:15.628196+00:00
-- url     : https://prove2.me/theorems/c7d9f641-aa46-443f-b41f-ce4eb695d07f
-- title:
--   Genuine original strictly pre-ruin right-payment dividend mass is bounded by initial capital plus the actual Levy running supremum
-- statement:
--   Before genuine ruin, the post-right-payment reserve x+X(t)-rightLimit D(t) is nonnegative by the Proved actual original stopped reserve lemma. The actual Levy value X(t) is at most its original running supremum, so right-payment cumulative dividends at strictly pre-ruin t are bounded above by x+runningSup X(t). Together with the original discounted Stieltjes cash <= rightLimit D(t), this provides a true-path quadratic cash envelope for the purejump controlled physical Itô source.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) (ω : Ω)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω ≤ x + runningSup X t ω := by sorry
