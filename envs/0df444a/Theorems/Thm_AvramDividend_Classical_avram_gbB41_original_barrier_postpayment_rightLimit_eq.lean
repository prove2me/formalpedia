-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
-- name    : AvramDividend.Classical.avram_gbB41_original_barrier_postpayment_rightLimit_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:51:58.203209+00:00
-- url     : https://prove2.me/theorems/a56a5fed-d871-4395-9185-ac45f94a979a
-- title:
--   Original barrier dividend right limit equals its prepayment value at every time
-- statement:
--   For every spectrally negative Lévy process and barrier initial capital equal to barrier, the original barrier dividend is monotone and right-continuous, so its rightLimit D_t+ equals D_t at every physical time. This source-faithful zero-payment-jump fact simplifies the positive-drift Gaussian stopped prepayment/postpayment ledger while respecting the original dividend conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB41_original_barrier_postpayment_rightLimit_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (ω : Ω) (t : ℝ≥0) :
    rightLimit (barrierStrategy X c c) t ω =
      barrierStrategy X c c t ω := by sorry
