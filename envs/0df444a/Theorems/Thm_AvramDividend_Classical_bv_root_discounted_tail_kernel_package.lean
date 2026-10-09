-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_package
-- name    : AvramDividend.Classical.bv_root_discounted_tail_kernel_package
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:18:07.644455+00:00
-- url     : https://prove2.me/theorems/5c0d50ec-08f3-4e49-9fa7-e5aff075b26f
-- title:
--   Root-shifted BV renewal kernel has positive support and total mass strictly below drift
-- statement:
--   At the positive Esscher root, construct the nonnegative-support tail-density measure κφ associated with the jump-magnitude measure weighted by exp(-φz). Prove it is SFinite, supported on x≥0, has total mass strictly below BV drift δ, and has exact positive Laplace transform ∫exp(-φz)(1-exp(-sz))/s ν_mag(dz) for every s>0. The source-complete proof composes the two separately authored tail-kernel mass and Laplace lemmas with the remotely proved original-process subcriticality theorem. This isolates an exact geometric-convolution-ready measure package for the last open root-shifted renewal Laplace construction.
-- source:
--   Published positiveLaplace_esscher_discounted_tail_kernel, esscher_tail_kernel_mass_as_discounted_first_moment, bv_esscher_root_subcritical_kernel_mass and pinned Mathlib withDensity_absolutelyContinuous.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_root_discounted_tail_kernel_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ),
      SFinite κ ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by sorry
