-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
-- name    : AvramDividend.Classical.avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:46:22.881289+00:00
-- url     : https://prove2.me/theorems/def7cb73-ab3a-435f-bede-77a19fef63dd
-- title:
--   Original finite-activity Levy exponential factorises into intrinsic Gaussian, drift and physical jump factors
-- statement:
--   On one original source conull event at all times, the real exponential of the actual Levy path equals the product of the exponentials of its intrinsic Gaussian residual, finite-activity signed drift and actual physical jump series.
-- source:
--   Proved A35 original physical Gaussian source identity, Mathlib Real.exp_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (θ : ℝ),
      Real.exp (θ * X.X t ω) =
        Real.exp (θ * R t ω) *
        Real.exp (θ * ((t : ℝ) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) *
        Real.exp (θ * (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0)) := by sorry
