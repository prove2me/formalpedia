-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_standardize_zero_variance
-- name    : EthierKurtz.kmt_affine_standardize_zero_variance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:46:55.635652+00:00
-- url     : https://prove2.me/theorems/37e33009-1d4e-4372-b2d8-cf26de05263e
-- title:
--   Affine standardization at zero variance
-- statement:
--   If a real probability law has an exponential moment near zero and variance zero, represent it as a point mass using scale zero, while choosing a fixed centered, unit-variance Gaussian law with exponential moments as the standardized law.
-- source:
--   Degenerate case of Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_affine_standardize_zero_variance
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by sorry

end EthierKurtz
