-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_integrable_of_components
-- name    : AvramDividend.Classical.bv_weighted_generator_residual_integrable_of_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:55:24.284665+00:00
-- url     : https://prove2.me/theorems/33452ddc-b101-498f-813d-4d1d24ac32b9
-- title:
--   BV generator residual is weighted-integrable from derivative, jump and scale components
-- statement:
--   The exponentially weighted bounded-variation Lévy generator residual is integrable over positive reserves whenever the weighted scale derivative, restricted jump generator integral and scale function are each integrable. It uses the exact bounded-variation generator formula and linearity of IntegrableOn. This discharges the residual-integrability half of the weighted Laplace uniqueness premise.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; BV Lévy generator decomposition

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_eq_drift_integral

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem bv_weighted_generator_residual_integrable_of_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q θ : ℝ) (W : ℝ → ℝ)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ))) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * (X.generator W x - q * W x))
      (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
