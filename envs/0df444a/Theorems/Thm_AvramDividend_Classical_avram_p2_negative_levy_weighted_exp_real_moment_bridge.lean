-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_real_moment_bridge
-- name    : AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_real_moment_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:02:51.142192+00:00
-- url     : https://prove2.me/theorems/f33f33d2-a12d-41dd-9399-4c259775b11a
-- title:
--   Actual negative Lévy weighted-image moments equal ofReal real Lévy exponential integrals
-- statement:
--   For each polynomial degree, the ENNReal moment of the finite fourth-weighted negative Lévy measure X.ν pushed forward by exp equals the ENNReal of its corresponding integrable real tilted exponential ν-integral. Source-side integrability follows from the existing finite image measure and the independently proved nonnegative-tilt domination, with no jump-count or compensator premises. This provides the exact limit-side moment identification needed to combine original moment convergence with compact-support uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_real_moment_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) =
    ENNReal.ofReal (∫ y in Iio (0 : ℝ),
      Real.exp ((k : ℝ) * y) * (Real.exp y - 1) ^ 4 ∂X.ν) := by sorry
