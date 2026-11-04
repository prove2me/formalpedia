-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula
-- name    : AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:24:28.973588+00:00
-- url     : https://prove2.me/theorems/b0cbde28-c089-43c0-9328-d98583ef4039
-- title:
--   Source negative Lévy weighted exponential image has exact polynomial moments
-- statement:
--   Every polynomial moment of the finite weighted exp-pushforward of the original negative Lévy measure is exactly the Lévy integral of exp(k y)(exp(y)-1)^4 over strictly negative marks. Uses pinned Mathlib integration under map and withDensity on X.ν itself. Together with the already Proved original-space weighted exp(X_t) moment formula, supplies the two sides needed for the full finite-measure moment-convergence identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) =
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal ((Real.exp y - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp y) ^ k) ∂X.ν) := by sorry
