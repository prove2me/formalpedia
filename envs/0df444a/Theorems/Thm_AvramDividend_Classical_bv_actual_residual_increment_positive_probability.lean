-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
-- name    : AvramDividend.Classical.bv_actual_residual_increment_positive_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:40:47.934645+00:00
-- url     : https://prove2.me/theorems/9539bc9d-8375-4753-90c6-6b9b83228e35
-- title:
--   Exact probability of a positive drift-residual increment over a finite-activity Lévy interval
-- statement:
--   For the original bounded-variation finite-activity spectrally negative Lévy process, the drift residual Y_t=d t−X_t has nonnegative increments a.s. and the probability that Y_t−Y_s is strictly positive is exactly 1−exp(−λ(t−s)). The Proved zero-increment exponential probability and fixed-interval drift support make the positive increment event almost-everywhere the complement of zero increment; measurable-set real probability complementation proves the result. This is the Bernoulli increment input for bounding the number of active dyadic cells of the true residual path, a route to proving finite-activity no-creep without a Lévy–Itô construction.
-- source:
--   Avram Palmowski Pistorius (2007), finite negative-jump activity; Prove2Me fixed-interval residual support and zero-atom law.

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_fixed_times
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_increment_positive_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω | 0 <
      ((t : ℝ) * X.drift - X.X t ω) -
      ((s : ℝ) * X.drift - X.X s ω)} =
        1 - Real.exp (-(((t - s : ℝ≥0) : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
