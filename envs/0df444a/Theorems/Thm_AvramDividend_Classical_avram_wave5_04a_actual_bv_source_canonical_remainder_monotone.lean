-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:18:48.249737+00:00
-- url     : https://prove2.me/theorems/019edf01-4961-4bf1-805e-b935366106bb
-- title:
--   Actual BV Levy source has a single nondecreasing canonical residual after subtracting its entire jump series
-- statement:
--   For the actual bounded-variation spectrally negative Levy source, on one full event, the time-indexed real path t times source drift minus X_t minus the complete negative original left-jump magnitude series over (0,t] is nondecreasing. It is therefore an explicit, coherent, nonnegative downward finite-variation source component across arbitrary overlapping and stopped intervals. The result does not force it to vanish, and does not use a Poisson replacement or the controlled Ito-Meyer formula.
-- source:
--   Wave5 Chat04-A; original-source C proved e84d1832-1a90-4b40-a0ca-e0f4065fdb5e, original interval jump bound proved 0ebd2a44-06bf-4a28-a9db-4e70c0ac84c8; pinned ENNReal.tsum_add and toReal_add for disjoint jump intervals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual BV downward finite-variation remainder is one coherent,
nondecreasing original-process path after subtracting every source left jump.
No pure-jump equality or independent Poisson realisation is imposed. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) := by sorry
