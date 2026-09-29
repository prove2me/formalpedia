-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_image_moments
-- name    : EthierKurtz.kmt_affine_image_moments
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:59:51.589335+00:00
-- url     : https://prove2.me/theorems/0a940d5b-a799-42e9-a108-0f3b7ff4f18c
-- title:
--   Moments of an affine image of a standardized law
-- statement:
--   If a probability law is the affine image y ? m + sig�y of a centered, unit-variance law, then its mean is m and its variance is sig�.
-- source:
--   Affine change-of-variables identities for the first two moments.

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz
theorem kmt_affine_image_moments
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1) :
    MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) = m /\
      variance (fun y : Real => y) (mu : Measure Real) = sig ^ 2 := by
  sorry
end EthierKurtz
