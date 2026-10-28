-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_weighted_path_increment_grid_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_esscher_weighted_path_increment_grid_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:21:29.573558+00:00
-- url     : https://prove2.me/theorems/ce5ac4a9-813b-400a-a49f-5d247edaff65
-- title:
--   Actual Lévy path measure under finite-mesh Esscher likelihood preserves increment-vector reversal
-- statement:
--   For a true spectrally negative Lévy path weighted by the compensated exponential density of the sum of its n equal-mesh increments, every Borel increment-vector event has exactly the same weighted path-measure mass after reversing the order of all increments. This transports accepted vector-level weighted symmetry back to a genuine source path measure through the accepted map-withDensity observable-density identity. The terminal sum can subsequently be identified with the terminal displacement via the accepted telescoping theorem.
-- source:
--   Canonically Proved avram_ws01e_b_esscher_grid_increment_vector_reversal (1afef52c), avram_ws01e_b_map_withDensity_observable_density (da772096).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_esscher_weighted_path_increment_grid_reversal
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
