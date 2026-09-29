-- Prove2me | Theorems.Thm_EthierKurtz_kmt_affine_standardize
-- name    : EthierKurtz.kmt_affine_standardize
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:13:58.195186+00:00
-- url     : https://prove2.me/theorems/d4d73198-494d-4d85-9af4-9419227b3e2f
-- title:
--   Standardizing a law with an exponential moment
-- statement:
--   Represent every real probability law with an exponential moment near zero as an affine image of a centered, unit-variance law with an exponential moment near zero. At zero variance, use a fixed centered unit-variance law and scale zero.
-- source:
--   Reduction lemmas for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

theorem kmt_affine_standardize
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
    ∃ (ν : ProbabilityMeasure Real) (m σ : Real),
      0 ≤ σ ∧
      Measure.map (fun y : Real => m + σ * y) (ν : Measure Real) = (μ : Measure Real) ∧
      MeasureTheory.integral (ν : Measure Real) (fun y : Real => y) = 0 ∧
      variance (fun y : Real => y) (ν : Measure Real) = 1 ∧
      (Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
        Integrable (fun y : Real => Real.exp (a * y)) (ν : Measure Real)) := by
  sorry

end EthierKurtz
