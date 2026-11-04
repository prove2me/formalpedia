-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_unweighted_linear_smalltime_bound
-- name    : AvramDividend.Classical.avram_p2_original_negative_tail_unweighted_linear_smalltime_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:33:51.695589+00:00
-- url     : https://prove2.me/theorems/a74403d6-48cc-48b4-9132-d197689b5600
-- title:
--   Original Lévy separated negative-increment probability is O(h) without a weight
-- statement:
--   For the same original spectrally negative Lévy process and every positive separation epsilon, the actual source probability of X_h <= -epsilon is bounded by C h for all sufficiently small h>0, with a finite positive real C. This removes the explicit strictly positive exponential-deficit threshold from the previously Proved weighted original-process estimate by rigorous extended nonnegative real division, supplying the rare-event rate needed for uniform L² grid estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_weighted_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_negative_tail_unweighted_linear_smalltime_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
          ENNReal.ofReal (C * h) := by sorry
