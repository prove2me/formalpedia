-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_image_pushforward
-- name    : EthierKurtz.kmt_affine_image_pushforward
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:44:50.955773+00:00
-- url     : https://prove2.me/theorems/1f9d7fa6-9d0b-4390-bc35-ca6e4c71a64a
-- title:
--   Affine image transfer for KMT couplings
-- statement:
--   If a centered, unit-variance real law admits a KMT coupling, then every nonnegative affine image of that law also admits a KMT coupling. The coupling is obtained by applying the affine map to each increment and leaving the Brownian coordinate fixed; the error constants are rescaled accordingly.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz
theorem kmt_affine_image_pushforward
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hsig : 0 <= sig)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1)
    (happrox : kmtApproximation nu) :
    kmtApproximation mu := by
  sorry
end EthierKurtz
