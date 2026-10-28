-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_finite_laplace_package_ac
-- name    : AvramDividend.Classical.bv_esscher_root_finite_laplace_package_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:00:47.174529+00:00
-- url     : https://prove2.me/theorems/0bec4f4f-d645-4133-b80e-7c9bfd3384ee
-- title:
--   Esscher BV finite renewal Laplace package retaining Lebesgue absolute continuity
-- statement:
--   Strengthen the canonically Proved BV Esscher root finite-Laplace renewal measure construction by retaining absolute continuity of the positive half-line restriction of its finite measure. Reuse the Proved absolutely continuous discounted root jump-tail kernel and uniform geometric renewal AC package, retaining the exact all-large-s real Laplace equality. This enables a direct strengthen-and-reuse of the canonical cumulative scale identity, then corrected bv_ac_esscher_scaled_renewal_kernel_series_data (9be5ada9), BV continuous renewal density, C1, finite cstar, and the Avram Dividend root.
-- source:
--   Accepted bv_esscher_root_finite_laplace_package argument 04a1385f, with canonically proved bv_root_discounted_tail_kernel_ac_package and positive_finite_supported_geometric_renewal_uniform_ac.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_laplace_denominator_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_bv_esscher_discounted_jump_product_integrable
import Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform_ac
import Theorems.Thm_AvramDividend_Classical_esscher_root_real_positive_geometric_factor
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_finite_laplace_package_ac {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (β : Measure ℝ) (b : ℝ),
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
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
