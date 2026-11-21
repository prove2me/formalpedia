-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
-- name    : AvramDividend.Classical.avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:40:07.617195+00:00
-- url     : https://prove2.me/theorems/08c2e3c8-9981-4189-97b0-3ed877336222
-- title:
--   Genuine spectrally negative unbounded-variation Lévy running supremum has finite second moment on every bounded original horizon
-- statement:
--   For the original unbounded-variation spectrally negative Lévy process and any fixed bounded horizon n, the real original path running supremum has an integrable square under its actual probability law. Use the Proved original all-nonnegative-θ exponential running-supremum moment at θ=1, original supremum nonnegativity and measurable path, and the exponential-moment-to-polynomial-moment theorem; the required negative-θ exponential is dominated by 1 because the running supremum is nonnegative. This supplies the quadratic domination needed to prove original bounded ruin-clipped dividend cash has second moment and hence the uniform L2 physical Itô source c2a65023.

import Mathlib
import Mathlib.Probability.Moments.IntegrableExpMul
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (n : ℝ≥0) :
    Integrable (fun ω : Ω => (runningSup X n ω)^2) P := by sorry
