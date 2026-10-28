-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
-- name    : AvramDividend.Classical.bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:21:52.791346+00:00
-- url     : https://prove2.me/theorems/6fbd417b-37fb-4d3e-a5c7-cba18134e113
-- title:
--   BV Lévy drift deficit is negligible in probability on inverse-frequency small-time meshes
-- statement:
--   For any bounded-variation spectrally negative Lévy process X with drift d, let δ_n≥0 and frequencies θ_n≥1 satisfy θ_n→∞ and δ_n θ_n=c. Then for each a>0, the probability that θ_n(δ_n d-X_{δ_n})≥a tends to zero. This is an unconditional convergence-in-probability theorem for the actual Lévy sample-path drift deficit, including infinite-activity jump measures. It combines a.e monotone BV deficit paths, the already Proved exact small-time Laplace expectation limit, and an a.e Laplace-tail convergence principle.
-- source:
--   Proved bv_drift_deficit_ae_monotone_all_times UUID bdb273f0, bv_scaled_deficit_laplace_tendsto_one_ws01b UUID 8777bdb6 and laplace_large_deficit_probability_tendsto_zero_ae_ws01b UUID bf65d8a5 (once canonically Proved). Kyprianou, scale-function theory, BV decomposition.

import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_tendsto_zero_ae_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_scaled_deficit_laplace_tendsto_one_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω |
        a ≤ θ n * ((δ n : ℝ) * X.drift - X.X (δ n) ω)})
      atTop (𝓝 (0 : ℝ)) := by sorry
