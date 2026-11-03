-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_rightContinuous
-- name    : AvramDividend.Classical.avram_wave8_20_original_postpayment_reserve_rightContinuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T20:08:52.09031+00:00
-- url     : https://prove2.me/theorems/c0b55139-c148-403f-81de-0d9edbf80ffb
-- title:
--   Original Lévy controlled post-rightpayment reserve has pathwise right continuity at every time
-- statement:
--   For every original spectrally negative Levy process and dividend strategy, the physical postpayment reserve x+X(t)-D(t+) is right continuous at every nonnegative time along each sample path. The theorem supports right-approaching bounded stopping-time approximations and interior localisation for W8-04 without assuming the target stochastic verification inequality.
-- source:
--   Original stochastic BV verification support for Proposition 4(i). The genuine shifted Levy path is right continuous by accepted source theorem 984180e2; the original dividend right limit is right continuous by bba8dbb3. Their arithmetic difference is right continuous without using stopped supermartingale inequality, HJB or optional sampling.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_postpayment_reserve_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (Ici t) t := by sorry
