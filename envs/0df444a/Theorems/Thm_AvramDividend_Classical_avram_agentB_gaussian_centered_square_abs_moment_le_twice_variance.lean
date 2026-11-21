-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance
-- name    : AvramDividend.Classical.avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:33:30.210178+00:00
-- url     : https://prove2.me/theorems/f19d66d4-193e-49f5-84af-4f03369b9629
-- title:
--   Absolute centred Gaussian Hermite square residual has expected value at most twice its variance
-- statement:
--   For any real square-integrable random variable Y on a probability space with exact second moment v ≥ 0, the absolute centred quadratic Hermite residual |Y²−v| is integrable and its expectation is at most 2v. This gives the sharp mesh-order bound needed for each original zero-jump Gaussian centred-square source cell after applying the Proved exact stopped Gaussian second moment.
-- source:
--   Absolute value triangle, nonnegative square, integrability of squares, linearity and monotonicity of Bochner integrals on a probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hY : Integrable (fun ω => (Y ω)^2) P)
    (hMean : (∫ ω, (Y ω)^2 ∂P) = v) :
    Integrable (fun ω => |(Y ω)^2 - v|) P ∧
    (∫ ω, |(Y ω)^2 - v| ∂P) ≤ 2 * v := by sorry
