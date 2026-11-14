-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b109_original_no_negative_band_implies_jumpfree_from_spectral_noPos
-- name    : AvramDividend.Classical.avram_b109_original_no_negative_band_implies_jumpfree_from_spectral_noPos
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:05:36.569196+00:00
-- url     : https://prove2.me/theorems/85baf7bc-d649-45f1-b355-adfb0f0bbfbb
-- title:
--   Original spectral negativity and voidness of every negative cutoff force every actual stopped-interval source jump to vanish
-- statement:
--   For every original spectrally negative Levy source sample path and arbitrary genuine half-open interval (s,t], suppose no source jump belongs to any prescribed negative cutoff band at most -1/(n+1). The proved original cadlag theorem supplies the left-limit convergence at every positive physical time. The defining noPosJumps field therefore proves each actual source jump is nonpositive. A nonzero source jump would be strictly negative and must fall into some negative cutoff band because the reciprocal thresholds tend to zero. Contradiction. Hence the original path is genuinely jumpfree on the interval. This discharges the hNoPos premise of B108 directly from the canonical source definition, with no extra stochastic moment, independence or null-event hypotheses.
-- source:
--   Original SpectrallyNegativeLevy.noPosJumps field, Proved avram_p2_a_zero_rate_original_cadlag_regular_all_times, real reciprocal cutoff convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Absence of every original negative cutoff source mark gives genuine jumpfree intervals on paths with no positive jumps. -/

theorem AvramDividend.Classical.avram_b109_original_no_negative_band_implies_jumpfree_from_spectral_noPos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (hNoBand : ∀ n : ℕ, ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
