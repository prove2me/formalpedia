-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
-- name    : AvramDividend.Classical.chat04_lower_clock_weak_survival_past_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:23:07.374831+00:00
-- url     : https://prove2.me/theorems/604b702f-041e-4920-8fa6-781326c492e2
-- title:
--   Weak survival to the lower-crossing clock equals absence of strictly earlier downward crossing
-- statement:
--   For every actual spectrally negative Lévy path and finite nonnegative horizon t, t≤τ_lower^- is equivalent to the absence of strict downward reserve crossings at all earlier times s<t. This is a precise pathwise interface between the strict downcrossing infimum stopping clock and the pre-horizon history predicate. It makes no Wiener-Hopf, scale-harmonicity or exit-formula assumptions, and is a prerequisite to proving almost-everywhere equivalence of strict-clock killing and whole-history killing in the stochastic half-line resolvent.
-- source:
--   Canonically Proved lowerCrossingClock_lt_horizon_iff_exists_witness 07415c4f-541a-41c1-9aa5-41b562447fbf, plus negation of linear-order strict comparison. Careful at t=τ: the result uses s<t, not s≤t.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Mathlib.Order.CompleteLattice.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_lower_clock_weak_survival_past_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ)
    (ω : Ω) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ twoSidedExitDownTime X lower ω ↔
      ∀ s : ℝ≥0, s < t → lower ≤ X.X s ω := by sorry
