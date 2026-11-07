-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f18_original_stopped_postpayment_reserve_upper_bound
-- name    : AvramDividend.Classical.avram_f18_original_stopped_postpayment_reserve_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:05:48.80196+00:00
-- url     : https://prove2.me/theorems/54e82fb2-6014-4f9e-ae1c-cc28271ea41b
-- title:
--   Original post-payment reserve at a bounded Lévy stopping clock is bounded above
-- statement:
--   For the original spectrally negative Lévy process and a valid original monotone dividend strategy, the source-exact pre/post-ruin branch reserve at any clock with X(t)≤K is at most x+K. This proves compact upper control for the original infinite-cap localised terminal.
-- source:
--   Actual original-process pathwise financial reserve; links F14 first-upcrossing clocks to F15 compact upper-potential bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_f18_original_stopped_postpayment_reserve_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (K : ℝ) (hK : X.X t ω ≤ K) :
    (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω) ≤ x + K := by sorry
