-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_finite_activity_global_intrinsic_martingale_fields
-- name    : AvramDividend.Classical.avram_p4_f11_finite_activity_global_intrinsic_martingale_fields
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:35:19.582814+00:00
-- url     : https://prove2.me/theorems/535fac89-153f-4a75-a36f-1fb6ed5acf6d
-- title:
--   Global physical Gaussian and small-jump intrinsic martingale fields in finite-activity Levy model
-- statement:
--   For actual finite-negative-jump Levy process with standing hypotheses, construct globally defined R and Jsmall as a.e. intrinsic residual limits, prove fixed-time integrability and martingale properties, and exact Levy drift plus Gaussian, small-band and large-jump decomposition. Derive from proved b213 with empty marked grid, independent of a finite-stopping-clock range.
-- source:
--   Proved Avram b213 19339df6, specialised to empty grid for original finite-activity stopped Ito branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_finite_activity_global_intrinsic_martingale_fields
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)

 :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) := by sorry
