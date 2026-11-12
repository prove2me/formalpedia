-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_original_tail_variance_from_finite_strip_isometry
-- name    : AvramDividend.Classical.avram_ja22_original_tail_variance_from_finite_strip_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:06:26.458961+00:00
-- url     : https://prove2.me/theorems/e5df71c0-32fe-4051-9929-6f7de6896c16
-- title:
--   Original omitted-tail exact variance follows from finite-strip isometry and almost sure limit
-- statement:
--   Analytic L2 limit passage: if every original finite cutoff strip has exact quadratic isometry and the physical truncated residuals converge almost surely to R, then the omitted-nearzero tail R_n minus R has exact limiting variance.
-- source:
--   J-A22 physical noise strand. This is a pure limit passage, conditional on an original-process finite-band identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_original_tail_variance_from_finite_strip_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (hStrip : ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
