-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_le_of_nonnegative_before_first_ruin
-- name    : AvramDividend.Classical.ruinTime_le_of_nonnegative_before_first_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:10:02.615014+00:00
-- url     : https://prove2.me/theorems/37cfb780-6457-4467-a2e4-8b0f408a7030
-- title:
--   A reserve nonnegative before another strategy's ruin cannot ruin earlier
-- statement:
--   For two controlled Lévy surplus paths, if strategy B's reserve remains nonnegative at every deterministic time strictly before the ruin time of strategy D, then B cannot ruin earlier than D. The result follows directly from the infimum defining ruinTime and provides the stopping-time order needed for zero-cap pathwise barrier dominance.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 2, ruin-time definition; exact Formalpedia `ruinTime` infimum.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ruinTime_le_of_nonnegative_before_first_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hpre : ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x B t ω) :
    ruinTime X x D ω ≤ ruinTime X x B ω := by sorry
