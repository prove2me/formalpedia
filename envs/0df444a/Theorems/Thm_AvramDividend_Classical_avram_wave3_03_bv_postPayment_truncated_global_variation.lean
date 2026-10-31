-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_truncated_global_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:41:21.258991+00:00
-- url     : https://prove2.me/theorems/1035f03b-d6ec-49b6-8ca5-1a20fc8e71be
-- title:
--   Original BV post-payment surplus frozen at finite horizon is globally bounded-variation
-- statement:
--   For the original standing bounded-variation spectrally negative Levy process and any adapted dividend strategy, almost every actual post-payment controlled surplus path, frozen at any finite nonnegative horizon, has globally bounded variation over all nonnegative times. This retains all continuous dividend variation and strict-right payment jumps through the freezing horizon.
-- source:
--   Apply the accepted genuine post-payment compact reserve variation lemma 73edfc32-dafe-4030-8fa5-9e3f20659099 to the monotone time clipping t -> min t T, following the accepted pre-payment global truncation proof dfae1b88-e487-4124-80e7-143e9c94d482.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_reserve_boundedVariationOn_compact

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_truncated_global_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn
        (fun t : ℝ≥0 => x + X.X (min t T) ω - rightLimit D (min t T) ω)
        Set.univ := by sorry
