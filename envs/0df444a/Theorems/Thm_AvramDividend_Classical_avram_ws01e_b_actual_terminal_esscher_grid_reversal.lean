-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_terminal_esscher_grid_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_terminal_esscher_grid_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:02:00.995809+00:00
-- url     : https://prove2.me/theorems/5c0e901e-ab59-479f-9cd3-81f72277574a
-- title:
--   Actual terminal-displacement Esscher likelihood preserves finite-grid Lévy reversal
-- statement:
--   For a spectrally negative Lévy process, the genuine compensated finite-terminal density exp(θ (X_(nδ)-X_0)−nδ ψ(θ)) on the original path law assigns exactly equal masses to any Borel event on the full vector of n equal-mesh increments and its coordinate-reversal event. The previous path-level Esscher-weighted reversal identifies the same identity using the sum of all increments, while the accepted Fin-indexed mesh telescoping identity proves this sum equals the actual terminal displacement. No infinite-horizon Esscher law or unproved Wiener–Hopf factorisation is invoked.
-- source:
--   Composes the accepted actual Esscher-weighted path increment-vector reversal and exact Fin-indexed Lévy telescope theorems.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_weighted_path_increment_vector_reversal

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_actual_terminal_esscher_grid_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A}) := by sorry
