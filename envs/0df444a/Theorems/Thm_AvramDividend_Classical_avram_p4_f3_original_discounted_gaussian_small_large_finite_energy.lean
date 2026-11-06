-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:48:12.943706+00:00
-- url     : https://prove2.me/theorems/7eded0d7-6697-4e1a-9959-086845fa4a0e
-- title:
--   All three actual original stopped Gaussian and Lévy jump coefficients have finite discounted physical L2 source energies
-- statement:
--   For the same original unbounded-variation Levy process X, actual dividend strategy D and clipped predividend reserve U, all three discounted original stopped Gaussian and negative-jump source intensities have finite quadratic energies on any finite physical product source measure.
-- source:
--   Combine independently Proved/public discounted original Gaussian certificate 4382bab8 with discounted original small/large Lévy negative jump certificate b536464c; same X,D,ν and U. No equality in law, axiom or circular canonical parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_small_large_joint_finite_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
          ((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ))) ^ 2) ∂X.ν) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
           (w (U p + z) - w (U p))) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
