-- Prove2me | Theorems.Thm_EthierKurtz_kmt_zero_variance_measure_is_dirac
-- name    : EthierKurtz.kmt_zero_variance_measure_is_dirac
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T21:07:12.877073+00:00
-- url     : https://prove2.me/theorems/3577120a-62d9-4074-b418-1a1bd198be6b
-- title:
--   Zero variance implies a point mass
-- statement:
--   For a real probability law with an exponential moment near the origin, zero variance forces the law to be a point mass.
-- source:
--   Auxiliary lemma for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz
theorem kmt_zero_variance_measure_is_dirac
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun m : Real => Measure.map (fun _ : Real => m) (mu : Measure Real) = (mu : Measure Real) := by sorry
end EthierKurtz
