-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_gaussian_small_jump_joint_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_physical_clipped_gaussian_small_jump_joint_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:46:34.950198+00:00
-- url     : https://prove2.me/theorems/802e6cde-946b-4261-8faa-45ed38823bfc
-- title:
--   Physical original pre-dividend clipped reserve has simultaneous Gaussian and compensated small-jump finite quadratic energy
-- statement:
--   For the same original physical X, D, time sample pair and compact clipping of its actual pre-dividend left reserve, the Gaussian Ito coefficient and negative small-jump coefficient have finite quadratic energies for any finite physical source measure.
-- source:
--   Combines already accepted original clipped Gaussian gradient finite energy with original physical clipped negative band jump finite source energy; the exact same physical left-limit reserve appears in both.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_predividend_negative_band_joint_L2_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_physical_clipped_gaussian_small_jump_joint_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U p + z) - w (U p)) -
          (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
