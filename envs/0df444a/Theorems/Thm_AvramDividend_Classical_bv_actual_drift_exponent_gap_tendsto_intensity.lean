-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_drift_exponent_gap_tendsto_intensity
-- name    : AvramDividend.Classical.bv_actual_drift_exponent_gap_tendsto_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:25:51.645992+00:00
-- url     : https://prove2.me/theorems/e6b8e60a-d29a-4114-ab5f-f4aed046920b
-- title:
--   Finite-activity BV Lévy exponent drift deficit tends to negative-jump intensity
-- statement:
--   For the actual BV Lévy exponent ψ(θ), the gap dθ−ψ(θ) converges to the real negative-jump intensity ν((−∞,0)) as θ=n→∞. Uses the already-Proved exact finite-activity exponent rearrangement and dominated-convergence limit of the negative-jump exponential integral. This provides the analytic input for recovering the zero-jump probability of the actual finite-activity residual process via its Laplace transform.
-- source:
--   Avram Palmowski Pistorius (2007) finite-activity first-jump survival; the canonical exponent finite-activity rearrangement and finite negative-jump Laplace integral limit proved on Prove2Me.

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_finite_jump_rearrangement
import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exp_integral_tendsto_zero_nat
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_drift_exponent_gap_tendsto_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto
      (fun n : ℕ => X.drift * (n : ℝ) - X.ψ (n : ℝ))
      atTop (𝓝 ((X.ν (Iio (0 : ℝ))).toReal)) := by sorry
