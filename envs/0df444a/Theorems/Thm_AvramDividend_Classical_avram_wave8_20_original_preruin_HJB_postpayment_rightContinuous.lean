-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
-- name    : AvramDividend.Classical.avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:40:40.949006+00:00
-- url     : https://prove2.me/theorems/634baba4-5288-4652-a7ea-42f4ce32b9e9
-- title:
--   Original pre-ruin postpayment HJB test is right-continuous along source strict-survival clocks
-- statement:
--   Before the genuine source-controlled ruin time, the HJB candidate evaluated on the original post-rightpayment reserve is right-continuous along all future times that still strictly precede ruin. This follows from actual Lévy and dividend path regularity plus source solvency, independently of any stopped supermartingale inequality. It is the proper right-approach interface for W8-04 and does not impose continuity at a ruin discontinuity.
-- source:
--   Original Avram bounded-variation stopped localisation. The newly accepted pathwise postpayment reserve right continuity and accepted pre-ruin postpayment solvency compose with the exact HJB candidate ContinuousOn (Ici 0). The domain is the physical sample-specific source strict-survival right set and avoids claiming global continuity across ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => w (x + X.X s ω - rightLimit D s ω))
      {s : ℝ≥0 | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω} t := by sorry
