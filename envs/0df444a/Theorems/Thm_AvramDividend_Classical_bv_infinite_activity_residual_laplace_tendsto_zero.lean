-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_residual_laplace_tendsto_zero
-- name    : AvramDividend.Classical.bv_infinite_activity_residual_laplace_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:59:16.449596+00:00
-- url     : https://prove2.me/theorems/9bc4d762-3b0e-41ae-8dab-28c285a257d7
-- title:
--   Infinite Lévy jump activity annihilates the positive-time drift-residual Laplace limit
-- statement:
--   For a bounded-variation spectrally negative Lévy process with infinitely many negative jumps in Lévy intensity, the Laplace transform of the nonnegative drift deficit at any fixed positive time converges to zero as its parameter increases through positive integers. This direct exponent argument avoids assumptions about Poisson jump-count laws.
-- source:
--   Accepted theorems bv_exponent_drift_deficit_tendsto_atTop, bv_actual_levy_drift_normalised_laplace and bv_exponent_negative_jump_deficit_exact; Mathlib exponential convergence.

import Theorems.Thm_AvramDividend_Classical_bv_exponent_drift_deficit_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_residual_laplace_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Real.exp ((n : ℝ) * (X.X t ω - (t : ℝ) * X.drift)) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
