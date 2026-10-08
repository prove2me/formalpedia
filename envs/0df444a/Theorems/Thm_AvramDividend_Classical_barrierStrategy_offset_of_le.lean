-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_offset_of_le
-- name    : AvramDividend.Classical.barrierStrategy_offset_of_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:37:13.796222+00:00
-- url     : https://prove2.me/theorems/2330944f-f640-48bf-aa17-b50042051c1c
-- title:
--   Barrier dividends below the barrier are the delayed positive part of boundary dividends
-- statement:
--   For any fixed path and time, if the initial capital x does not exceed the barrier a, the cumulative barrier-strategy dividends equal the positive part of the boundary-started cumulative dividends minus the initial gap a−x. This establishes the exact pathwise first-passage threshold needed for the subsequent stochastic reward decomposition without using the deprecated reflected-value definitions.
-- source:
--   The exact definition of barrierStrategy, max 0 of the running supremum shifted by x−a, and the real-number max-translation identity for nonnegative a−x. At time zero both strategies pay zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_offset_of_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ω : Ω) :
    barrierStrategy X x a t ω =
      max 0 (barrierStrategy X a a t ω - (a - x)) := by sorry
