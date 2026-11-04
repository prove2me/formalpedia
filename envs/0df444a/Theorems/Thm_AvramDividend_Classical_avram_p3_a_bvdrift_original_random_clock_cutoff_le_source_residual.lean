-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_random_clock_cutoff_le_source_residual
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_random_clock_cutoff_le_source_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:45:44.191211+00:00
-- url     : https://prove2.me/theorems/3bc5b1b3-01b3-40a1-9001-cd6548effb9a
-- title:
--   Original BV source drift dominates actual negative-jump cutoff across sample-dependent stopped clocks
-- statement:
--   For any sample-dependent pair of almost-surely ordered clocks on the genuine original Levy sample space, the truncated actual left-jump magnitude sum between the two clocks is at most the original physical BV drift-minus-path difference, with no additional independence, stopping-time, adaptedness, compensator or representation assumptions.
-- source:
--   The full original BV source jump bound 0ebd2a44 holds simultaneously over all deterministic intervals on one probability-one event, allowing samplewise substitution of random clocks. Monotonicity of ENNReal tsum under cutoff gives the bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original bounded-variation source jump cutoff is bounded at any two
almost-surely ordered sample-dependent clocks, without adaptedness premises. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_random_clock_cutoff_le_source_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (S U : Ω → ℝ≥0) (hSU : ∀ᵐ ω ∂P, S ω ≤ U ω) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0∞,
      (∑' (u : ℝ≥0),
        if S ω < u ∧ u ≤ U ω ∧
             ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        then ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal
        ((((U ω : ℝ≥0) : ℝ) * X.drift - X.X (U ω) ω) -
          (((S ω : ℝ≥0) : ℝ) * X.drift - X.X (S ω) ω)) := by sorry
