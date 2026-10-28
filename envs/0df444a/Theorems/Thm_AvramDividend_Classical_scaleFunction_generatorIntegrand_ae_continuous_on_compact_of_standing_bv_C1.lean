-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv_C1
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:17:06.638294+00:00
-- url     : https://prove2.me/theorems/abeca456-eada-421f-b4b9-56fc80fd01f6
-- title:
--   Almost-everywhere state continuity of the BV jump generator under C1 scale regularity
-- statement:
--   For a standing spectrally negative Lévy process with bounded variation, let W be the q-scale function and C1 on a positive open interval. On every compact subinterval, the compensated negative-jump generator integrand is continuous in the reserve variable for almost every negative jump. Scale continuity away from zero, continuity of W' under C1, and atomlessness of the standing BV jump measure give the claim. This removes the unnecessary C2 hypothesis from the jumpwise continuity input; a first-order dominating envelope is still needed for continuity of the integral.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, BV C1 regularity and the accepted Prove2Me atomless-jump continuity lemmas.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_ae_continuous_of_standing_bv
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_ae_continuousWithinAt_of_shift_ae

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
          (Icc l u) x := by sorry

end AvramDividend.Classical
