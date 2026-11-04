-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_marginal_laplace_equal_forces_exact_drift_jump_path
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_marginal_laplace_equal_forces_exact_drift_jump_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:02:23.116923+00:00
-- url     : https://prove2.me/theorems/1c3e1bc4-1577-4d39-bcf8-07c96f70b70a
-- title:
--   Two original marginal Laplace transforms identify exact BV physical drift and actual jumps
-- statement:
--   For the genuine original BV spectrally negative Levy source, if both exponential marginals of X at integer clocks (after subtracting its source physical drift) and its actual negative-jump tsum are integrable and have equal expectations, the original source path has exactly drift minus its actual negative jumps at every nonnegative time on one full-probability event. The equal-marginals condition is strictly weaker than a joint source/jump characteristic identity, and is explicitly assumed until the original source exponent and actual-jump marginal transform are separately proved. No auxiliary or manufactured process model is used.
-- source:
--   Use already Proved original residual monotonicity, exact time-zero jump function identity, exponential monotonicity to dominate original source exponential by actual jump-sum exponential, integral nonnegativity, equal integrals, integral_eq_zero_iff_of_nonneg_ae, exp_injective and integer-clock monotone sandwich.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_marginal_laplace_equal_forces_exact_drift_jump_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    let J : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
    (∀ n : ℕ, Integrable (fun ω =>
      Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift)) P) →
    (∀ n : ℕ, Integrable (fun ω =>
      Real.exp (-(J (n : ℝ≥0) ω))) P) →
    (∀ n : ℕ,
      (∫ ω, Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift) ∂P) =
      (∫ ω, Real.exp (-(J (n : ℝ≥0) ω)) ∂P)) →
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift - J t ω := by sorry
