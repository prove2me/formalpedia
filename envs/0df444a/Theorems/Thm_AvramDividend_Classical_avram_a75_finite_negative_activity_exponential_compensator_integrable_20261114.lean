-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a75_finite_negative_activity_exponential_compensator_integrable_20261114
-- name    : AvramDividend.Classical.avram_a75_finite_negative_activity_exponential_compensator_integrable_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:14:17.871854+00:00
-- url     : https://prove2.me/theorems/504df8b2-7239-4be3-b139-1d8bd5c7abf7
-- title:
--   Finite negative Lévy intensity controls original exponential deficit and truncated jump compensation integrability
-- statement:
--   Any finite measure on the strictly negative real marks has integrable exponential deficit e^(theta*y)-1 for every theta>=0, because 0<e^(theta*y)<=1. The standard Lévy truncation mark y*1_{(-1,1)}(y) is absolutely bounded by one on negative marks, so it is also integrable. Both estimates hold on the actual finite negative Lévy measure and discharge the exact hypotheses of A74.
-- source:
--   Finite-measure IsFiniteMeasure instance on ν.restrict(Iio 0), elementary Real.exp_le_one_iff and Set.indicator bounds, Mathlib Integrable.mono.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a75_finite_negative_activity_exponential_compensator_integrable_20261114
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) ν ∧
    IntegrableOn
      (fun y : ℝ => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) ν := by sorry
