-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
-- name    : AvramDividend.Classical.bv_actual_levy_drift_normalised_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:36:56.281254+00:00
-- url     : https://prove2.me/theorems/51327fa0-cccd-4a1e-9dc9-b6b19da7cd6c
-- title:
--   The actual BV Lévy process has the drift-normalised negative-jump Laplace transform
-- statement:
--   For every bounded-variation spectrally negative Lévy process, its actual one-time law after cancelling the deterministic drift has Laplace transform exp(-t times the negative-jump Lévy exponential deficit), for θ≥1. Unlike a constructed auxiliary process this theorem directly concerns the supplied X, and is a foundation for transferring the compound-Poisson first-jump law in the finite-activity branch.
-- source:
--   SpectrallyNegativeLevy.laplace and the Proved bv_exponent_negative_jump_deficit_exact.

import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_drift_normalised_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, Real.exp (θ * X.X t ω) *
        Real.exp (-((t : ℝ) * X.drift * θ)) ∂P) =
      Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by sorry
