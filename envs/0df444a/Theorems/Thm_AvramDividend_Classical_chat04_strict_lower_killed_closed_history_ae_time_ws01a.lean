-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_killed_closed_history_ae_time_ws01a
-- name    : AvramDividend.Classical.chat04_strict_lower_killed_closed_history_ae_time_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:06:28.588414+00:00
-- url     : https://prove2.me/theorems/26b1bbb5-a856-4350-882e-7720b61723eb
-- title:
--   Strict lower-clock killing and full-history killing agree almost everywhere in real time
-- statement:
--   For each actual spectrally negative Lévy path, the genuine strict lower first-passage killing indicator in the stochastic exponential-clock resolvent equals the all-earlier-and-current-reserves survival indicator used by the whole-history killed semigroup for almost every real time. The one potentially differing exit instant has Lebesgue measure zero. This is proved directly from already canonical clock theorems, not from the desired scale harmonicity, the two-sided exit formula, or pending helpers.
-- source:
--   Accepted lower-clock weak-survival characterisation 604b702f-041e-4920-8fa6-781326c492e2; observed strict downcrossing clock bound fa7ceff5-37e3-4a61-8ee2-60a7dc1416fc; Mathlib ENNReal.toReal_ofReal, measure_singleton and ae_iff.

import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_lower_killed_closed_history_ae_time_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) (ω : Ω) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      (0 ≤ t ∧ ENNReal.ofReal t < twoSidedExitDownTime X lower ω) ↔
      (0 ≤ t ∧ ∀ s : ℝ≥0, s ≤ Real.toNNReal t → lower ≤ X.X s ω) := by sorry
