-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_weighted_path_increment_vector_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_esscher_weighted_path_increment_vector_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:44:21.122155+00:00
-- url     : https://prove2.me/theorems/7c531ade-b3a9-401f-866c-97c03ddeba2f
-- title:
--   Actual Esscher-weighted path law has reversed finite-mesh Lévy increment-vector symmetry
-- statement:
--   For any genuine spectrally negative Lévy path, fixed finite equal time mesh, real Esscher parameter θ and Borel event A of the entire finite vector of Lévy increments, the original path measure weighted by exp(θ times the total grid-increment sum minus the horizon times Lévy exponent ψ(θ)) gives equal masses to A on the increments in forward order and to A on their reverse. It uses the now-Proved exact change-of-measure pushforward theorem and the explicit finite-mesh Esscher density vector reversal theorem, rather than postulating a new tilted process or Wiener–Hopf factorisation. A separate telescoping lemma identifies this grid sum with the terminal displacement.
-- source:
--   Proved avram_ws01e_b_map_withDensity_observable_density (da772096) and avram_ws01e_b_esscher_grid_increment_vector_reversal (1afef52c).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_esscher_weighted_path_increment_vector_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A} =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A} := by sorry
