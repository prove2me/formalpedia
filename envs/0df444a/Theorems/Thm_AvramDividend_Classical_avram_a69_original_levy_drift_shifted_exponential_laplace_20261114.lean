-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
-- name    : AvramDividend.Classical.avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:55:36.710371+00:00
-- url     : https://prove2.me/theorems/a7f49c73-991a-4157-b265-03933b4f740e
-- title:
--   Original Levy source drift-shifted Laplace transform and exponential integrability at every horizon
-- statement:
--   The original spectrally negative Levy source X has exponential integrability and exact Laplace transform after subtracting any deterministic shift d. The positive-ray law from its SpectrallyNegativeLevy structure transfers by multiplying by exp(-theta*d), yielding the exact shifted source exponent. This supplies the complete integrable-source-product identity needed in the physical marked Gaussian decomposition A65 without imposing jump independence.
-- source:
--   Immediate direct consequence of the original X.laplace field, Real.exp_add, and Bochner integral_const_mul. No external probability space or companion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ d : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * (X.X t ω - d))) P ∧
    (∫ ω, Real.exp (θ * (X.X t ω - d)) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ - θ * d) := by sorry
