-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:36:54.991219+00:00
-- url     : https://prove2.me/theorems/c4b53c7c-d769-4894-a0d8-c0b2a1516d1e
-- title:
--   Exact original bounded-variation source increments equal drift less all left jumps and one monotone residual
-- statement:
--   On one common probability-one event for the genuine original spectrally negative Levy source under bounded variation, explicitly construct its canonical nondecreasing residual R. For every ordered pair of source times the exact real source increment is drift multiplied by elapsed time minus the complete intrinsic negative left-jump magnitude series on that interval minus the increment of R. This is an original-process pathwise identity, not the assertion that R vanishes and not a Poisson substitute or controlled Ito-Meyer theorem.
-- source:
--   Avram Wave5 Chat04-A; imports canonical Proved source remainder 019edf01-4961-4bf1-805e-b935366106bb, left-jump additivity 7c727efc-2476-40eb-b00e-4b68802cfe1c, and actual BV jump dominance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_source_negative_jump_series_interval_add

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact original BV source increment decomposition into drift, all
intrinsic source left jumps and one monotone downward finite-variation
remainder. This theorem does not claim that the remainder vanishes. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (u : ℝ≥0),
              if s < u ∧ u ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
              else 0).toReal -
            (R t - R s) := by sorry
