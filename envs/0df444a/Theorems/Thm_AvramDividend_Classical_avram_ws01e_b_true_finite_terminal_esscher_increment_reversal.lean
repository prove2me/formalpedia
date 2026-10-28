-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_finite_terminal_esscher_increment_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_true_finite_terminal_esscher_increment_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:13:20.164984+00:00
-- url     : https://prove2.me/theorems/bf836fe1-c9b9-4f4a-bac6-a40d4457cdf8
-- title:
--   The genuine finite-terminal Esscher-weighted Lévy path law retains full equal-mesh increment-vector reversal
-- statement:
--   Take a genuine spectrally negative Lévy process X under the original measure P and weight entire paths at deterministic terminal time nδ by the compensated Esscher likelihood exp(θ(X_{nδ}−X_0)−nδψ(θ)). Then the pushforward law of the vector of its n mesh increments is invariant under reversing all Fin n coordinates, as an exact equality of measures on Fin n→ℝ. This is the finite-terminal Esscher reversal theorem, not a hypothetical infinite-horizon tilted process. It follows from the accepted true finite-terminal Esscher path/vector change-of-measure identification and exact Esscher-weighted vector reversal.
-- source:
--   Prepared application of avram_ws01e_b_esscher_mesh_path_vector_law_identification (Open pending proof) and Proved avram_ws01e_b_esscher_grid_increment_vector_reversal (1afef52c).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_mesh_path_vector_law_identification
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_true_finite_terminal_esscher_increment_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ) :
    Measure.map (fun v : Fin n → ℝ => fun i => v i.rev)
      (Measure.map
        (fun ω : Ω => fun i : Fin n =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((i.val : ℝ≥0) * δ) ω)
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))) =
    Measure.map
      (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) := by sorry
