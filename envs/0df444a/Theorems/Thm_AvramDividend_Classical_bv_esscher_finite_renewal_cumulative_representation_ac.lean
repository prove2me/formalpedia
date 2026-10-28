-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_finite_renewal_cumulative_representation_ac
-- name    : AvramDividend.Classical.bv_esscher_finite_renewal_cumulative_representation_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:09:11.802182+00:00
-- url     : https://prove2.me/theorems/ad8bafa2-e07a-42ca-b6b4-d7897fc1e328
-- title:
--   BV Esscher tilted scale cumulative has a positive-axis AC finite renewal measure
-- statement:
--   Strengthen the canonically Proved pointwise Esscher finite renewal cumulative representation: the finite renewal witness is absolutely continuous off zero. The new Proved bv_esscher_root_finite_laplace_package_ac provides the same exact scale and renewal real Laplace equality and β positive-axis absolute continuity. The old accepted deterministic uniqueness argument then gives the pointwise scale cumulative equality. This supports the continuous BV renewal-density identity, corrected root-connected bv_ac_esscher_scaled_renewal_kernel_series_data, standing C1 and cstar_lt_top.
-- source:
--   Accepted bv_esscher_finite_renewal_cumulative_representation proof 2b208bdd, strengthened with new canonical BV root finite-Laplace absolute continuity package.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_finite_laplace_package_ac
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Mathlib.Tactic.FunProp

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_esscher_finite_renewal_cumulative_representation_ac
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ β : Measure ℝ,
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal) := by sorry
