-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_zero_residual_all_times
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_zero_residual_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:45:25.896415+00:00
-- url     : https://prove2.me/theorems/033ca9a6-15ed-4c83-85e7-dc05d5ded825
-- title:
--   Integer-clock zero residual forces the exact original BV drift-jump decomposition at every time
-- statement:
--   For the actual bounded-variation spectrally negative Lévy source, almost-sure zero drift-minus-negative-jump residual at every nonnegative integer time implies that same residual vanishes for every real nonnegative time. Uses the existing source monotone residual and archimedean cofinality of natural times, without constructing an alternative process or assuming a full path representation.
-- source:
--   Accepted original-source canonical remainder monotonicity 019edf01-4961-4bf1-805e-b935366106bb and pinned Mathlib exists_nat_ge. It reduces the remaining P2 jump-Laplace identity from all real times to a countable integer-time family.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Countably many zero canonical residuals at integer times force zero at
all times along the same original monotone BV Levy source path. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_zero_residual_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hzeros : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal = 0 := by sorry
