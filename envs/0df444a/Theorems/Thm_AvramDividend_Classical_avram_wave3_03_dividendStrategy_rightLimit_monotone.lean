-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
-- name    : AvramDividend.Classical.avram_wave3_03_dividendStrategy_rightLimit_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:26:27.711947+00:00
-- url     : https://prove2.me/theorems/f7eef805-3be2-4d1e-9ca1-61e09a0f266e
-- title:
--   Actual post-payment dividend right-limit is nondecreasing at every sample path
-- statement:
--   Every genuine adapted monotone dividend strategy has a nondecreasing post-payment strict-right-limit process at each sample point, including the time-zero atom. This is needed for the BV controlled surplus partition variation bound.
-- source:
--   IsDividendStrategy path monotonicity and rightLimit as the conditional infimum over later times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_dividendStrategy_rightLimit_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) : Monotone (fun t : ℝ≥0 => rightLimit D t ω) := by sorry
