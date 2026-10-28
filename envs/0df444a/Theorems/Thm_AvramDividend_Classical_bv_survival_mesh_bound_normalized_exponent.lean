-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_survival_mesh_bound_normalized_exponent
-- name    : AvramDividend.Classical.bv_survival_mesh_bound_normalized_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:37:55.959989+00:00
-- url     : https://prove2.me/theorems/c60927d2-1ad4-44ac-baac-bb4e386f4548
-- title:
--   Normalize the actual BV strict-survival expected deficit mesh estimate using the exact Laplace exponent
-- statement:
--   For an actual bounded-variation spectrally negative Levy process, a uniform deterministic time mesh whose endpoints match the original capital deficit yields an exact upper bound on expected deficit restricted to strict zero-barrier survival. Use the proved genuine expected-survival finite mesh inequality, identify the negative jump exponential integral with drift*theta minus psi(theta), and normalise the drift-per-cell prefactor to a fixed constant.
-- source:
--   Proved bv_strict_survival_expected_deficit_uniform_mesh_bound and bv_exponent_negative_jump_deficit_exact.

import Theorems.Thm_AvramDividend_Classical_bv_strict_survival_expected_deficit_uniform_mesh_bound
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.bv_survival_mesh_bound_normalized_exponent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hEnd : ∀ ω, D N ω - D 0 ω =
      (T : ℝ) * X.drift - X.X T ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hStep : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hStepReal : ∀ k : ℕ, k < N →
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ))
    (a C : ℝ) (ha : 0 < a)
    (haEq : a = X.drift * (δ : ℝ))
    (hPref : 4 * a * (N : ℝ) = C)
    (hθ : 1 ≤ (1 / (2 * a) : ℝ))
    (hLeft : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => D N ω - D 0 ω)) P)
    (hRight : Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P)
    (hCellInt : ∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
      C * (1 - Real.exp (-((δ : ℝ) *
        (X.drift * (1 / (2 * a)) - X.ψ (1 / (2 * a)))))) := by sorry
