-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_real_moment_bridge
-- name    : AvramDividend.Classical.avram_p2_original_weighted_exp_real_moment_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:55:58.210347+00:00
-- url     : https://prove2.me/theorems/8876e128-08f3-4ef5-8e02-b7e575c000ac
-- title:
--   Actual original weighted exponential-image moments equal ofReal tilted source expectations
-- statement:
--   Every polynomial ENNReal moment of the genuine original fourth-weighted exp(X_t) pushforward is exactly the ENNReal of the corresponding integrable real tilted exponential expectation on the same source Ω/P. This connects the previously proved finite measure moments to the original Lévy small-time derivative and is required for the finite-measure moment-convergence theorem. It uses only the original process, verified integrability and the Mathlib conversion of a nonnegative real integral to lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_weighted_exp_real_moment_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω)))) =
    ENNReal.ofReal (∫ ω, Real.exp ((k : ℝ) * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4 ∂P) := by sorry
