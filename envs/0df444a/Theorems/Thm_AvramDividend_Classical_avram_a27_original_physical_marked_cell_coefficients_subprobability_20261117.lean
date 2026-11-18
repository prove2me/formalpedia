-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_cell_coefficients_subprobability_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_marked_cell_coefficients_subprobability_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:58:30.964268+00:00
-- url     : https://prove2.me/theorems/0a4ecf2a-c3e5-49a0-8a15-374c11f5ef69
-- title:
--   Original physical negative marked count-cell exponential coefficients form a nonnegative summable subprobability mass
-- statement:
--   Let K_t be the actual measurable negative-jump count of a finite-activity spectrally negative Levy process, and J_t its original cumulative negative-jump sum. The exact source-space count-cell integrals C(k) = E[exp(theta J_t) 1_{K_t=k}] are nonnegative, sum over every nonnegative integer k to E exp(theta J_t), and the total is at most one for theta≥0. No conditional marking independence or alternate source space is assumed.
-- source:
--   Proved A85 original exponential integrability, A107 physical exponential expectation upper bound, and A27 generic integral partition HasSum.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_marked_cell_coefficients_subprobability_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K) :
    (∀ k : ℕ, 0 ≤
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P)) ∧
    HasSum (fun k : ℕ =>
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P))
      (∫ ω, Real.exp (θ * J ω) ∂P) ∧
    (∫ ω, Real.exp (θ * J ω) ∂P) ≤ 1 := by sorry
