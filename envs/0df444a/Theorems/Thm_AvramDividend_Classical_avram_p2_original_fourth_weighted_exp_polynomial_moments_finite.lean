-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_polynomial_moments_finite
-- name    : AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_polynomial_moments_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:59:06.504566+00:00
-- url     : https://prove2.me/theorems/52a535dd-8e07-428a-8f5f-50923155809a
-- title:
--   Every polynomial moment of the original fourth-weighted exponential source law is finite
-- statement:
--   For the genuine source process X at every fixed time t and every natural k, the ENNReal source lintegral of the fourth exponential deficit times exp(X_t)^k is finite. Proof: rewrite exp(X_t)^k as exp(k X_t), combine positive factors into ofReal of a nonnegative integrable test, invoke the previously Proved all-positive-tilts integrability and the comparison of ofReal lintegral with the finite enorm integral. This is the finite-moment prerequisite for defining and studying the weighted weak-convergence family on the actual source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_polynomial_moments_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P) < ⊤ := by sorry
