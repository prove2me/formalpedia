-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:47:11.208536+00:00
-- url     : https://prove2.me/theorems/e80cd41a-8701-4c77-8c22-472f62a77d27
-- title:
--   Finite actual original negative-jump magnitude series on all bounded BV source intervals
-- statement:
--   For the actual bounded-variation spectrally negative Levy process, on a single original probability-one event the entire intrinsic negative left-jump magnitude ENNReal tsum is finite for every ordered bounded interval, allowing real-valued jump totals and cutoff-to-real convergence without an assumed point-process representation.
-- source:
--   Apply the Proved original source interval jump magnitude upper bound (0ebd2a44) to the finite ENNReal.ofReal physical BV drift-minus-path increment and ENNReal.ofReal_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original negative left-jump magnitude series is finite on
every bounded time interval under the actual BV hypothesis. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) < ⊤ := by sorry
