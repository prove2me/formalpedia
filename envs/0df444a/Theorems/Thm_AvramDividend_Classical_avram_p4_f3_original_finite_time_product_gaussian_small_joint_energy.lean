-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_finite_time_product_gaussian_small_joint_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_finite_time_product_gaussian_small_joint_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:23:57.450388+00:00
-- url     : https://prove2.me/theorems/b8aaab32-2cd5-4dee-aadc-04b80e4823b0
-- title:
--   Original finite time-measure by probability physical source jointly has Gaussian and small-jump quadratic energy
-- statement:
--   For the original Levy process and its actual controlled left-limit reserve, on any finite time measure multiplied by the original probability sample measure, both compactly clipped Gaussian and negative compensated-jump coefficients have finite joint quadratic energies. A concrete finite-horizon measure may be passed once its finite time volume is established.
-- source:
--   Instantiate Proved public 802e6cde for the actual product of finite time measure and original probability sample measure; prove product finiteness by typeclasses, without surrogate stochastic process. The declaration contains only the theorem signature, separate from the preamble, to meet import-at-top.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_gaussian_small_jump_joint_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_finite_time_product_gaussian_small_joint_energy
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
    (hK : ENNReal.ofReal K < C)
    (μtime : Measure ℝ≥0) [IsFiniteMeasure μtime] :
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
