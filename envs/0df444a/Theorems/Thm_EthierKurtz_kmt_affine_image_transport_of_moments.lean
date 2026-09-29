-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_image_transport_of_moments
-- name    : EthierKurtz.kmt_affine_image_transport_of_moments
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:59:51.714979+00:00
-- url     : https://prove2.me/theorems/ed994e66-eaba-4e0f-9fde-887841c18539
-- title:
--   Transport of a KMT coupling with prescribed image moments
-- statement:
--   Suppose a standardized law admits a KMT coupling, and an affine image has the matching mean and variance parameters. Then the affine image law also admits a KMT coupling, with the error constants adjusted to the affine scale.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz
theorem kmt_affine_image_transport_of_moments
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hsig : 0 <= sig)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1)
    (hmu_mean : MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) = m)
    (hmu_variance : variance (fun y : Real => y) (mu : Measure Real) = sig ^ 2)
    (happrox : kmtApproximation nu) :
    kmtApproximation mu := by
  sorry
end EthierKurtz
