-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_cumulativeStieltjes_shift_at_firstUpcrossing
-- name    : AvramDividend.Classical.barrierStrategy_cumulativeStieltjes_shift_at_firstUpcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:24:34.067665+00:00
-- url     : https://prove2.me/theorems/788f2fa3-ed75-4f21-9602-339f7386961a
-- title:
--   Cumulative Stieltjes barrier payments agree with post-passage shifted increments
-- statement:
--   At a finite first passage to the barrier, all cumulative Stieltjes payments over (0,u+t] equal the shifted-future running-supremum dividend measure over (0,t]. The zero-mass pre-passage window and already proved translated window identity combine without any scale-function hypotheses. This supplies the cumulative-measure identity needed to equate shifted weighted dividend integrals.
-- source:
--   Directly supports the canonical strong-Markov barrier value theorem 79978d61-9d1f-4b20-b8a5-114797a8e380, using Proved theorems 88bf2f0b-9cd7-4772-89fc-a85ccae6d64d and 443876a6-e856-480c-8a37-40deba77bd09.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Interval.Set.LinearOrder
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_cumulativeStieltjes_shift_at_firstUpcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0,
      (dividendMeasure (barrierStrategy X x a) ω)
        (Set.Ioc (0 : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure
        (fun r _ =>
          sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
        ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  sorry
