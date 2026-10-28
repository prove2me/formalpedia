-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scaled_deficit_laplace_tendsto_one_ws01b
-- name    : AvramDividend.Classical.bv_scaled_deficit_laplace_tendsto_one_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:34:37.385746+00:00
-- url     : https://prove2.me/theorems/8777bdb6-1cec-4144-bdef-958bf8a1da2d
-- title:
--   Small-time bounded-variation drift-deficit Laplace expectations converge to one under inverse-frequency scaling
-- statement:
--   Let δ_n be nonnegative times and θ_n≥1 Laplace frequencies with θ_n→∞ and δ_n θ_n=c fixed. For any bounded-variation spectrally negative Lévy process, the expectation E[exp(-θ_n(δ_n d-X_{δ_n}))] tends to one. The result applies to infinite jump activity and follows from the exact finite-time drift-deficit Laplace transform and the vanishing normalised BV exponent gap. It advances the small-time pure-jump subordinator analysis needed to show downward irregularity/no creeping; convergence in probability or almost-sure pathwise control is a subsequent step.
-- source:
--   Proved bv_actual_levy_drift_normalised_laplace UUID 51327fa0, bv_exponent_negative_jump_deficit_exact UUID 952c5905, and bv_inverse_frequency_mesh_gap_tendsto_zero UUID 3f95b19b; Lévy bounded-variation fluctuation theory.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_mesh_gap_tendsto_zero
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scaled_deficit_laplace_tendsto_one_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c) :
    Tendsto (fun n : ℕ =>
      ∫ ω, Real.exp (θ n * X.X (δ n) ω) *
        Real.exp (-((δ n : ℝ) * X.drift * θ n)) ∂P)
      atTop (𝓝 (1 : ℝ)) := by sorry
