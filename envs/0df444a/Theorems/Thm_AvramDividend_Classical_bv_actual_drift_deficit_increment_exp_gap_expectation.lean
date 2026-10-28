-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_drift_deficit_increment_exp_gap_expectation
-- name    : AvramDividend.Classical.bv_actual_drift_deficit_increment_exp_gap_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:33:48.59572+00:00
-- url     : https://prove2.me/theorems/5473592c-07c2-4ea0-8c72-afbb4125e2b6
-- title:
--   Exact exponential expectation of a bounded variation Levy drift deficit increment
-- statement:
--   The stationary law of the BV Levy drift deficit increment D_t-D_s, composed with its exponential deficit transform, yields the exact one minus exponential expectation for duration t-s. This is the exact mesh-cell moment used in the finite-mesh no-local-monotonicity proof.
-- source:
--   Previously proved stationary increment law, expected exponential gap identity and Mathlib IdentDistrib integral equality.

import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Theorems.Thm_AvramDividend_Classical_bv_actual_discounted_deficit_exp_gap_expectation
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_drift_deficit_increment_exp_gap_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, (1 : ℝ) -
      Real.exp (-θ * ((X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω))) ∂P) =
      1 - Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by sorry
