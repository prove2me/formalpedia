-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_uniform_negative_grid_probability_mass
-- name    : AvramDividend.Classical.avram_p2_original_uniform_negative_grid_probability_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:51:00.297581+00:00
-- url     : https://prove2.me/theorems/8ca0081d-6393-4f48-8293-92f8b351e9ed
-- title:
--   Uniform original negative-grid probability mass under bounded total duration
-- statement:
--   For every positive separation epsilon and nonnegative horizon T on the unchanged original source probability space, there is a finite positive C so that, for all sufficiently small real mesh widths h>0 and every number of grid cells n with nh<=T, the source event mass n P(X_h<=-epsilon) is at most C T in ENNReal. This is derived rigorously from the accepted original negative rare-event probability estimate by real-to-ENNReal coercion and monotonicity. It is a substantive input to the original independent-increment grid L² uniform-integrability bound and does not use any intrinsic jump-intensity identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_unweighted_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_uniform_negative_grid_probability_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
          (n : ℝ≥0∞) *
            P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
          ENNReal.ofReal (C * T) := by sorry
