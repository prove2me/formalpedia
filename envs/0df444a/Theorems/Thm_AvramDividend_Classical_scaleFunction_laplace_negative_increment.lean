-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_negative_increment
-- name    : AvramDividend.Classical.scaleFunction_laplace_negative_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:57:32.074422+00:00
-- url     : https://prove2.me/theorems/c3e60a69-db94-4dfb-9e72-e30e220d880d
-- title:
--   Laplace transform of a negative spatial increment of the q-scale function
-- statement:
--   For a q-scale function W, theta>=0 with psi(theta)>q, and any negative or zero spatial shift y, the integral over x>0 of exp(-theta*x)*(W(x+y)-W(x)) equals (exp(theta*y)-1)/(psi(theta)-q). Both weighted terms are integrable by the proved scale-function integrability and shift-integrability results, permitting subtraction under the integral. The identity follows by the proved shifted Laplace transform and the defining transform of W. This is the uncompensated finite-difference component of the Levy jump generator's Laplace transform; the small-jump derivative compensation still requires separate treatment.
-- source:
--   Exact fixed-jump difference transform derived from Avram–Palmowski–Pistorius q-scale Laplace transform (3.4) and the established negative-shift integral, as a step towards Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_laplace_negative_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * (W (x + y) - W x)) =
      (Real.exp (θ * y) - 1) * (X.ψ θ - q)⁻¹ := by sorry

end AvramDividend.Classical
