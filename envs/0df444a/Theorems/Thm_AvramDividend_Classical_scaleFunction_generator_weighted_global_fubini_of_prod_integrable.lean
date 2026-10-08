-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable
-- name    : AvramDividend.Classical.scaleFunction_generator_weighted_global_fubini_of_prod_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:36:00.469476+00:00
-- url     : https://prove2.me/theorems/1b6472d7-8a24-4d8b-b7cd-e1046bc78f91
-- title:
--   Global weighted generator Fubini from absolute product integrability
-- statement:
--   For any spectrally negative Lévy process, any function W and real weight θ, suppose (x,y)↦exp(-θx)generatorIntegrand(W,x,y) is integrable on the product of positive-state Lebesgue measure and the restricted negative-jump Lévy measure. Then the full-half-line Fubini exchange is valid: ∫_{x>0} exp(-θx)(∫_{y<0}generatorIntegrand ν(dy))dx equals ∫_{y<0}∫_{x>0}exp(-θx)generatorIntegrand dx ν(dy). The negative-jump Lévy measure is SFinite under its quadratic condition, established earlier. Applying Mathlib.integral_integral_swap to the product integrability hypothesis establishes Fubini without any separate unsupported stochastic or local-to-global assumption.
-- source:
--   Mathlib integral_integral_swap and the accepted SFinite negative-jump Lévy measure theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_weighted_global_fubini_of_prod_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν := by sorry

end AvramDividend.Classical
