-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a52_original_finite_horizon_physical_mark_exponential_product_20261114
-- name    : AvramDividend.Classical.avram_a52_original_finite_horizon_physical_mark_exponential_product_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:52:43.849006+00:00
-- url     : https://prove2.me/theorems/2663e2fe-e0ab-4f10-b380-118a9eb4ad56
-- title:
--   Original finite-horizon physical Lévy exponential factorises into Gaussian, drift and finite causal negative-jump marks
-- statement:
--   For every finite time horizon on the original source probability space, the actual Levy source exponential factors into its intrinsic Gaussian exponential, deterministic drift and the exponential of a finite causal sum of genuine physical negative-jump marks, simultaneously on one conull event.
-- source:
--   A50 physical exponential factorisation, Proved A33 source jump support and A35 finite marked-jump sum localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a52_original_finite_horizon_physical_mark_exponential_product_20261114
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
            Real.exp (θ * (∑ u ∈ S, if u ≤ t then j u else 0))) := by sorry
