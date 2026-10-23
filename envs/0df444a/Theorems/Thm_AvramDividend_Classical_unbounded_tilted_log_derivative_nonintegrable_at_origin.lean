-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_log_derivative_nonintegrable_at_origin
-- name    : AvramDividend.Classical.unbounded_tilted_log_derivative_nonintegrable_at_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:53:28.172924+00:00
-- url     : https://prove2.me/theorems/e209bcd5-dd1d-440e-afbc-38bc16b392cb
-- title:
--   Non-integrability of the full logarithmic derivative near the origin for an unbounded-variation tilted scale function
-- statement:
--   For a spectrally negative Levy process of unbounded variation, the q-scale function vanishes at zero and is positive immediately to its right. Consequently its positive Esscher tilt V tends to zero as x decreases to zero, while log V diverges to negative infinity. This forces the logarithmic derivative V'/V to be non-integrable over the whole positive half-line. Unlike integrability on each interval (x,infinity) for x>0, the integral over (0,infinity) includes the singular origin. This is the substantive analytic input needed to reduce the existing flat-tail target exactly as written to its zero-measure witness.
-- source:
--   Reduction of AvramDividend.Classical.unbounded_tilted_log_derivative_integrable_at_infinity; elementary logarithmic-derivative analysis at a zero endpoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_tilted_log_derivative_nonintegrable_at_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hVdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x) :
    ¬ IntegrableOn (fun y : ℝ => deriv V y / V y) (Ioi (0 : ℝ)) := by sorry
