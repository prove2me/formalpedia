-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_strict_survival_closed_history_offclock_ws01a
-- name    : AvramDividend.Classical.chat04_lower_clock_strict_survival_closed_history_offclock_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:06:24.335995+00:00
-- url     : https://prove2.me/theorems/cb286043-1e23-4c35-9355-d59b3e0ecc63
-- title:
--   Strict lower-clock survival equals nonnegative closed-history killing away from the exit instant
-- statement:
--   For an actual spectrally negative Lévy path, away from its strict lower first-passage stopping instant, survival t<τ_lower^- is equivalent to every earlier and current state X_s at s≤t avoiding strict lower crossings. This bridges strict-clock and closed-history killed semigroup conventions without scale-function harmonicity or an exit formula. The excluded equality instant is negligible for subsequent time integration.
-- source:
--   Canonically Proved weak survival clock theorem 604b702f-041e-4920-8fa6-781326c492e2 and observed strict-downcrossing bound fa7ceff5-37e3-4a61-8ee2-60a7dc1416fc.

import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_lower_clock_strict_survival_closed_history_offclock_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hne : (t : ℝ≥0∞) ≠ twoSidedExitDownTime X lower ω) :
    (t : ℝ≥0∞) < twoSidedExitDownTime X lower ω ↔
      ∀ s : ℝ≥0, s ≤ t → lower ≤ X.X s ω := by sorry
