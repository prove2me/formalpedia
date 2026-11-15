-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a54_original_physical_gaussian_drift_finite_marked_laplace_product_20261114
-- name    : AvramDividend.Classical.avram_a54_original_physical_gaussian_drift_finite_marked_laplace_product_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:56:33.310142+00:00
-- url     : https://prove2.me/theorems/640eca5f-80c6-4178-a41b-e15b06218b03
-- title:
--   Original finite-activity Levy exponential as Gaussian, drift and finite marked product
-- statement:
--   On each finite horizon and one original source conull event the Levy exponential factors into intrinsic Gaussian, deterministic signed drift and finite actual marked-jump product.
-- source:
--   A52 original finite horizon physical exponential and A53 deterministic finite marked-product identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a54_original_physical_gaussian_drift_finite_marked_laplace_product_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ (t : ℝ≥0), t ≤ T → ∀ θ : ℝ,
          Real.exp (θ * X.X t ω) =
            Real.exp (θ * R t ω) *
            Real.exp (θ * ((t : ℝ) *
              (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) *
            (∏ u ∈ S, if u ≤ t then Real.exp (θ * j u) else 1)) := by sorry
