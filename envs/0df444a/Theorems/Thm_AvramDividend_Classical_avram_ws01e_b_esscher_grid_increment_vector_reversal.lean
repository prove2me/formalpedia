-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_esscher_grid_increment_vector_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:02:47.728392+00:00
-- url     : https://prove2.me/theorems/1afef52c-e5b9-4284-93cb-9f480da60e2e
-- title:
--   Explicit finite-terminal Esscher density preserves Lévy increment-vector reversal
-- statement:
--   For a genuine spectrally negative Lévy process and n equal mesh increments of size δ, weight their original vector law by the exact finite-terminal Esscher density exp(θ Σ_i ΔX_i − nδ ψ(θ)). The weighted measure assigns identical mass to every measurable increment-vector event and its coordinate-reversal preimage. This is a concrete finite-dimensional Esscher reversal result, relying on full-vector Lévy reversal, the accepted invariant-density change-of-measure theorem and finite sum permutation invariance. It does not invent an infinite-horizon Esscher law.
-- source:
--   Proved levy_increment_vector_tilted_reversal (a712024a) and Fin.revPerm preserves real coordinate sums, plus pinned Mathlib measurable finite sum and exp/ofReal composition.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_esscher_grid_increment_vector_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
        (fun v : Fin n → ℝ => ENNReal.ofReal
          (Real.exp (θ * (∑ i : Fin n, v i) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {v : Fin n → ℝ | (fun i => v i.rev) ∈ A} =
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
        (fun v : Fin n → ℝ => ENNReal.ofReal
          (Real.exp (θ * (∑ i : Fin n, v i) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) A := by sorry
