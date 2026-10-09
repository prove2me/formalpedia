-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_full_halfline_jump_fubini_of_slice_quadratic_bound
-- name    : AvramDividend.Classical.scaleFunction_full_halfline_jump_fubini_of_slice_quadratic_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:23:45.073129+00:00
-- url     : https://prove2.me/theorems/cd301b2f-ce33-41dc-b053-25054e131c7b
-- title:
--   Full Lévy generator Fubini from a quadratic bound on discounted state slices
-- statement:
--   Assume joint measurability and state-slice integrability of the discounted compensated jump generator. If, for almost every negative jump y, the positive-state integral of the norm is bounded by C min(1,y²), the Lévy moment condition and Fubini justify interchange of the full positive-state and negative-jump integrals. Unlike pointwise factorised bounds, this condition can accommodate a narrow origin-crossing boundary layer.
-- source:
--   Pinned Mathlib Fubini and the accepted slice-wise quadratic product-integrability theorem, for the Avram Dividend generator Laplace proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_full_halfline_jump_fubini_of_slice_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ C : ℝ)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))))
    (hsections : ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))),
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y)
        (Ioi (0 : ℝ)))
    (hnorm_meas : AEStronglyMeasurable
      (fun y : ℝ => ∫ x in Ioi (0 : ℝ),
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖)
      (X.ν.restrict (Iio (0 : ℝ))))
    (hdom : ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))),
      (∫ x in Ioi (0 : ℝ),
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖) ≤
          C * min 1 (y ^ 2)) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y)
      ∂X.ν := by sorry

end AvramDividend.Classical
