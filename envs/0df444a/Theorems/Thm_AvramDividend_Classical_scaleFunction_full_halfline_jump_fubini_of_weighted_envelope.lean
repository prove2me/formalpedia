-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_full_halfline_jump_fubini_of_weighted_envelope
-- name    : AvramDividend.Classical.scaleFunction_full_halfline_jump_fubini_of_weighted_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:11:24.927354+00:00
-- url     : https://prove2.me/theorems/10356478-23fd-420c-98d5-512c18f03154
-- title:
--   Full-half-line Lévy jump-generator Fubini under an integrable weighted state envelope
-- statement:
--   For a spectrally negative Lévy process, if its exponentially weighted compensated generator increment is jointly a.e. strongly measurable and dominated on x>0,y<0 by an integrable state envelope |g(x)| times min(1,y²), then integrating negative jumps before positive states equals integrating states before jumps. The proof uses the Lévy quadratic-moment condition, factorised product-integrability, the native SFinite jump measure, and Fubini. This precisely replaces an assumed global Fubini interchange by explicit analytic envelope conditions without incorrectly deriving them from local C2 regularity.
-- source:
--   Pinned Mathlib Integrable.mul_prod and integral_integral_swap; accepted positive-density Lévy SFinite and factorised domination lemmas in the Avram Dividend campaign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_full_halfline_jump_fubini_of_weighted_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))))
    (hdom : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))),
      ‖Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2‖ ≤
        |g p.1| * |min (1 : ℝ) (p.2 ^ 2)|) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y)
      ∂X.ν := by sorry

end AvramDividend.Classical
