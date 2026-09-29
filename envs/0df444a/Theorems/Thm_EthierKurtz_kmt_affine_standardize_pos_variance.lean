-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_standardize_pos_variance
-- name    : EthierKurtz.kmt_affine_standardize_pos_variance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:46:51.601508+00:00
-- url     : https://prove2.me/theorems/d15a1b08-62e8-47c2-9f89-9838f302d74a
-- title:
--   Affine standardization at positive variance
-- statement:
--   If a real probability law has an exponential moment in a neighborhood of zero and strictly positive variance, then centering by its mean and scaling by its standard deviation yields a probability law with mean zero, variance one, and an exponential moment in a neighborhood of zero; the original law is the corresponding affine image.
-- source:
--   Reduction lemma for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_affine_standardize_pos_variance
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by sorry

end EthierKurtz
