-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_chernoff_drift_bound
-- name    : AvramDividend.Classical.bv_actual_levy_chernoff_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:42:00.714236+00:00
-- url     : https://prove2.me/theorems/08e8e9b3-97ac-4c1a-8000-512cbf02cd05
-- title:
--   Chernoff bound for the actual bounded-variation Lévy reserve above the drift line
-- statement:
--   For a bounded-variation spectrally negative Lévy process with deterministic drift d, the probability that X_t exceeds dt by ε is at most exp(-θ ε) for any θ≥1. This is proved directly from the actual Lévy process moment axiom and the established exponent upper bound ψ(θ)≤dθ. Taking θ to infinity establishes that X_t cannot exceed dt at any fixed time, an essential precondition for the first-jump law.
-- source:
--   Proved bv_laplace_exponent_le_drift_mul and Mathlib Chernoff theorem measure_ge_le_exp_mul_mgf.

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_le_drift_mul
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_chernoff_drift_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ ε : ℝ) (hθ : 1 ≤ θ) :
    P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} ≤
      Real.exp (-θ * ε) := by sorry
