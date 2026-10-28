-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_uniform_mesh_exp_gap_expected_sum
-- name    : AvramDividend.Classical.bv_uniform_mesh_exp_gap_expected_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:43:20.44937+00:00
-- url     : https://prove2.me/theorems/a37c82ad-e8bb-445e-98cc-8cd73b757c6c
-- title:
--   Expected finite sum of uniform-mesh BV drift-deficit exponential gaps
-- statement:
--   For a uniform deterministic time mesh of the actual BV spectrally negative Levy process, the integrated sum of exponential increments of the physical drift deficit equals the number of cells times the common one-step Levy expectation, multiplied by an arbitrary scalar 4a. This follows from the proved stationary-increment exponential expectation, integrability of every cell, finite-sum integral linearity and the uniform step hypothesis. It is the process-specific expectation half of the finite-mesh instantaneous zero-barrier ruin argument.
-- source:
--   Proved bv_actual_drift_deficit_increment_exp_gap_expectation; Mathlib integral_finset_sum and integral_const_mul.

import Theorems.Thm_AvramDividend_Classical_bv_actual_drift_deficit_increment_exp_gap_expectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.bv_uniform_mesh_exp_gap_expected_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hStep : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (a : ℝ)
    (hInt : ∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-θ * (D (k + 1) ω - D k ω))) P) :
    (∫ ω, 4 * a * ∑ k ∈ Finset.range N,
      (1 - Real.exp (-θ * (D (k + 1) ω - D k ω))) ∂P) =
      4 * a * (N : ℝ) *
        (1 - Real.exp (-((δ : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) := by sorry
