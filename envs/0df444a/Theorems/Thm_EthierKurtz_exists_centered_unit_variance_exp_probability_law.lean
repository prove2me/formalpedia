-- Prove2me | Theorems.Thm_EthierKurtz_exists_centered_unit_variance_exp_probability_law
-- name    : EthierKurtz.exists_centered_unit_variance_exp_probability_law
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T21:07:13.112291+00:00
-- url     : https://prove2.me/theorems/3e4fd76b-94fa-4264-a1cc-a06ab289175f
-- title:
--   A standardized law with exponential moments
-- statement:
--   There exists a real probability law with mean zero, variance one, and finite exponential moments in a neighborhood of the origin; the symmetric two point law gives an example.
-- source:
--   Auxiliary construction for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz
theorem exists_centered_unit_variance_exp_probability_law :
    Exists fun (nu : ProbabilityMeasure Real) =>
      And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))) := by sorry
end EthierKurtz
