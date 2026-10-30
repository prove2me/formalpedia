-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_stationary_strict
-- name    : AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_stationary_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:38:17.766857+00:00
-- url     : https://prove2.me/theorems/95a5f015-2566-4f38-8513-82cc21d97db4
-- title:
--   The actual canonical drifted Brownian process has stationary increments at positive durations
-- statement:
--   The canonical Brownian process on gaussianLimit, normalised at its initial value and given deterministic drift minus one, has identically distributed increments for every pair of strictly ordered nonnegative times. This lifts the accepted general Brownian Gaussian-law equality to the actual canonical projective-limit process via the proved real-time Brownian bridge. It supplies the stationary increment hypothesis of the source SpectrallyNegativeLevy constructor.
-- source:
--   Proved drift-minus-one Brownian stationary positive increments theorem 646ddfc2-0c92-4a4b-9f39-96562dafb474, canonical real-time bridge 6b447517-ee65-42fd-aa06-1faa205162a5. Exact source reached intended remote sentinel, private job ceb1d86e-ac48-4369-af20-ae907094ab8f, SHA 57c770a8737daae69934177027e7289e1996698eeae95a5129bc22c2d972328e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_brownian_stationary_positive_increments

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_stationary_strict (s t : ℝ≥0) (hst : s < t) :
    IdentDistrib
      (fun ω : ℝ≥0 → ℝ =>
        (brownian t ω - brownian 0 ω - (t : ℝ)) -
        (brownian s ω - brownian 0 ω - (s : ℝ)))
      (fun ω : ℝ≥0 → ℝ =>
        brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
      gaussianLimit gaussianLimit := by sorry
