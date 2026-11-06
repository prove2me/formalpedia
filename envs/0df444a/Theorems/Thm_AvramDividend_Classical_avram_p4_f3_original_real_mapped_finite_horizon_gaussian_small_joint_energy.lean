-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_real_mapped_finite_horizon_gaussian_small_joint_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_real_mapped_finite_horizon_gaussian_small_joint_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:36:36.501485+00:00
-- url     : https://prove2.me/theorems/ea2b8809-9db3-438b-984a-740c54a5d2e9
-- title:
--   Actual finite real Lebesgue horizon mapped to nonnegative original time has Gaussian and small-jump joint finite energy
-- statement:
--   For the true original levy source X and dividend D, take Lebesgue real time restricted to [0,T], map it to NNReal, multiply by original P, and derive simultaneous Gaussian and small-negative-jump coefficient finite energies. The finite time-volume and finite product-measure conditions are proved, not assumed.
-- source:
--   After the public finite-time product lemma b8aaab32 is Proved, instantiate it with ((volume:Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal. Real Lebesgue restricted bounded interval is finite, and Measure.isFiniteMeasure_map preserves finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_finite_time_product_gaussian_small_joint_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_real_mapped_finite_horizon_gaussian_small_joint_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (T : ℝ≥0) :
    let μtime : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let μ : Measure (ℝ≥0 × Ω) := μtime.prod P
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U p + z) - w (U p)) -
          (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
