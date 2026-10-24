-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_right_jump_positive
-- name    : AvramDividend.Classical.barrierStrategy_initial_right_jump_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:33:24.471654+00:00
-- url     : https://prove2.me/theorems/8ca9a9f5-6cb9-4214-bd27-12854572c573
-- title:
--   The barrier dividend path has a positive initial right jump above the barrier
-- statement:
--   For any spectrally negative Levy sample path and any initial reserve x strictly above the barrier a, the barrier dividend strategy has a strictly positive right jump at time zero. Its jump size is exactly x-a. This is the deterministic initial lump sum and explains why the unrestricted right-continuity assertion for all x,a≥0 fails when x>a. No process expectation or Markov argument is required.
-- source:
--   Consequence of Proved AvramDividend.Classical.barrierStrategy_right_increment_formula, UUID 8d23d801-85d6-465e-8450-4011e0dabd54; corrects the scope of Open barrierStrategy_right_continuous_nonnegative_barrier UUID 11865c2a-6684-4cb0-bfaf-417066bf31b5.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_right_jump_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hax : a < x)
    (ω : Ω) :
    0 < rightLimit (barrierStrategy X x a) 0 ω -
        barrierStrategy X x a 0 ω := by sorry
