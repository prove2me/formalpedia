-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_ruin_clock_negative_band_jump_set_finite
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_ruin_clock_negative_band_jump_set_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:44:36.317915+00:00
-- url     : https://prove2.me/theorems/2fb423e3-f608-4a96-96c3-340de3c3d3d2
-- title:
--   Original negative-band intrinsic jump set is finite at any bounded sample-dependent ruin clock
-- statement:
--   For the original spectrally negative Lévy process, the separated negative-band intrinsic jump-time set remains finite at each sample-dependent clock τ bounded by deterministic T. This gives the finite-set substrate needed to form genuine pathwise stopped finite-band stochastic sums, with no clock measurability assumption or law-replacement.
-- source:
--   Exact Proved original finite-horizon negative-band jump set e5e6f70b-a901-43ba-b2bc-56911d56899f and Set.Finite.subset through τ(ω)≤T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_ruin_clock_negative_band_jump_set_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T) (ω : Ω) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.Finite := by sorry
