-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_image_transfer
-- name    : EthierKurtz.kmt_affine_image_transfer
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:14:12.322404+00:00
-- url     : https://prove2.me/theorems/72bcd0a0-c242-4a42-91e8-a5e08520cd78
-- title:
--   Affine transport of a KMT coupling
-- statement:
--   Transport the KMT coupling conclusion from a centered, unit-variance law to its affine image, preserving the Brownian coordinate and rescaling the error constants.
-- source:
--   Reduction lemmas for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

theorem kmt_affine_image_transfer
    (μ ν : ProbabilityMeasure Real) (m σ : Real)
    (hσ : 0 ≤ σ)
    (hmap : Measure.map (fun y : Real => m + σ * y) (ν : Measure Real) = (μ : Measure Real))
    (hmean : MeasureTheory.integral (ν : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (ν : Measure Real) = 1)
    (happrox : kmtApproximation ν) :
    kmtApproximation μ := by
  sorry

end EthierKurtz
