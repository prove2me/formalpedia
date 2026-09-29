-- Prove2me | Theorems.Thm_EthierKurtz_affine_standardize_exp_moment
-- name    : EthierKurtz.affine_standardize_exp_moment
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T21:02:20.625911+00:00
-- url     : https://prove2.me/theorems/4bd7920d-9bab-4b3c-8fae-1254ba9f9b0c
-- title:
--   Affine transforms preserve local exponential integrability
-- statement:
--   If a real probability law has a finite exponential moment for all parameters in some neighborhood of zero, then the inverse image law under any affine map with positive scale also has a finite exponential moment in a neighborhood of zero.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356; exponential-moment preservation under centering and positive scaling.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz
theorem affine_standardize_exp_moment
    (mu nu : ProbabilityMeasure Real) (m sigma : Real)
    (hsigma : 0 < sigma)
    (hmap : Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real))) :
    Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)) := by sorry
end EthierKurtz
