-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_explicit_geometric_scale_laplace
-- name    : AvramDividend.Classical.bv_esscher_explicit_geometric_scale_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:33:03.552158+00:00
-- url     : https://prove2.me/theorems/c390f500-f969-44c4-8e9f-cd648d71faf3
-- title:
--   Explicit BV Esscher geometric renewal measure has the q-scale Laplace transform
-- statement:
--   Carry one and the same explicit geometric convolution-power measure through the bounded-variation Esscher Laplace denominator identity, obtaining equality of all large-discount real Laplace transforms with the tilted q-scale function. The measure's finite total mass and positive-axis absolute continuity are preserved, allowing the right-continuity uniqueness theorem to give the exact pointwise scale identity required by the corrected renewal-density branch.
-- source:
--   Source-adapted exact accepted proof of bv_esscher_root_finite_laplace_package_ac (8a2d6f0f) combined with the now Proved explicit-kernel convolution-power package.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_explicit_geometric_laplace_ac
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_laplace_denominator_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_bv_esscher_discounted_jump_product_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_root_real_positive_geometric_factor
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_explicit_geometric_scale_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ) (b : ℝ),
      κ ≪ volume ∧
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal X.drift)⁻¹ ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-(φ * x)) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-(φ * x)) * W x)) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal)) := by sorry
