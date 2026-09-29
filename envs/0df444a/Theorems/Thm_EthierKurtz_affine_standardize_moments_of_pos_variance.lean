-- Prove2me | Theorems.Thm_EthierKurtz_affine_standardize_moments_of_pos_variance
-- name    : EthierKurtz.affine_standardize_moments_of_pos_variance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T21:02:23.066838+00:00
-- url     : https://prove2.me/theorems/d55ab51d-490d-4964-a18b-d7d73e8bd6f8
-- title:
--   Centering and scaling a positive-variance law
-- statement:
--   Every real probability law with strictly positive variance can be represented as the affine image of a probability law whose mean is zero and variance is one. The scaling factor is strictly positive.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356; moment-standardization component.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz
theorem affine_standardize_moments_of_pos_variance
    (mu : ProbabilityMeasure Real)
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 < sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (variance (fun y : Real => y) (nu : Measure Real) = 1))) := by sorry
end EthierKurtz
