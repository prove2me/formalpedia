-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:36:01.288207+00:00
-- url     : https://prove2.me/theorems/aea85c2b-51f7-4ac4-b4c9-badfe2c633ce
-- title:
--   Actual bounded-variation negative Lévy integrability of any endpoint-zero exponential polynomial
-- statement:
--   For every polynomial Q with Q(1)=0, Q(exp y) is Bochner integrable against the ORIGINAL negative Lévy measure under the actual BV source hypothesis, despite potentially infinite jump activity. Rewrite Q as the exact integrated zero-constant polynomial exponential primitive and use the previously Proved genuine BV integrability. No global first moment of ν is assumed.
-- source:
--   Proved zero-polynomial primitive representation and genuine BV primitive Lévy integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (Q : Polynomial ℝ) (hQ : Polynomial.eval 1 Q = 0) :
    IntegrableOn (fun y : ℝ => Polynomial.eval (Real.exp y) Q)
      (Set.Iio (0 : ℝ)) X.ν := by sorry
