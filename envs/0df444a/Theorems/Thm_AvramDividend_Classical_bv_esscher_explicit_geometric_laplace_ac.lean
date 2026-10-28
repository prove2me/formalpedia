-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_explicit_geometric_laplace_ac
-- name    : AvramDividend.Classical.bv_esscher_explicit_geometric_laplace_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:24:12.422954+00:00
-- url     : https://prove2.me/theorems/c55c3dab-0a5d-4c87-ba0c-3ba233da4cc8
-- title:
--   BV Esscher discounted-jump renewal kernel with explicit convolution powers and exact Laplace data
-- statement:
--   Expose a single common BV Esscher jump-tail kernel and its exact weighted convolution-power renewal measure, retaining the kernel's discounted-jump Laplace equation and the finite renewal cumulative Laplace transform. This bridges existing root-driven stochastic transform analysis to the real-density renewal series required for scale identification 1ca4a724-85b7-48bf-bae4-37890ef7055b.
-- source:
--   Root-specific combination of the canonically Proved BV root discounted-tail kernel and explicit geometric convolution-power Laplace package.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_explicit_powers_laplace_ac
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_explicit_geometric_laplace_ac
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ),
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
            ENNReal.ofReal
              ((1 - Real.exp (-(s * (z : ℝ)))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) ∧
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal X.drift)⁻¹ ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ,
                ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by sorry
