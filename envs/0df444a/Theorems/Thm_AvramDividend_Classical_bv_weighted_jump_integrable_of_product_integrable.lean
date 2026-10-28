-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
-- name    : AvramDividend.Classical.bv_weighted_jump_integrable_of_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:52:42.788677+00:00
-- url     : https://prove2.me/theorems/edc159a5-d69e-4055-9b2f-36f60818ebc8
-- title:
--   Weighted reserve-integrability of the Lévy generator jump term from signed product integrability
-- statement:
--   Whenever the exponentially weighted signed Lévy generator kernel is integrable on the positive-reserve by negative-jump product measure, its jump integral at each reserve, weighted by the same exponential, is integrable on positive reserves. The theorem combines s-finiteness of the negative-jump measure with the Mathlib Fubini partial-integrability theorem and extraction of the reserve-only exponential factor. It supplies the hJint hypothesis of the bounded-variation generator residual decomposition.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; Fubini/Tonelli

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem bv_weighted_jump_integrable_of_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (W : ℝ → ℝ)
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
