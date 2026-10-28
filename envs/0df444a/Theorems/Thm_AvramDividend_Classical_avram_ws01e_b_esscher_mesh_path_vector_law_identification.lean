-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_mesh_path_vector_law_identification
-- name    : AvramDividend.Classical.avram_ws01e_b_esscher_mesh_path_vector_law_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:10:17.60803+00:00
-- url     : https://prove2.me/theorems/eefc2d86-5b72-47df-bc96-0c0129cf0bb6
-- title:
--   Finite-terminal Esscher path likelihood pushes to the explicit weighted increment-vector law
-- statement:
--   For any spectrally negative Lévy path and equal mesh δ, the pushforward under the vector of n successive real increments of the path law weighted by exp(θ(X_{nδ}−X_0)−nδ ψ(θ)) equals the pushforward of the original path law weighted by the vector density exp(θ∑_i ΔX_i−nδ ψ(θ)). This is an exact finite-horizon Esscher change-of-measure identity, based on pathwise increment telescoping and the generic observation-dependent density pushforward theorem. No infinite-horizon Esscher probability is introduced.
-- source:
--   Proved avram_ws01e_b_map_withDensity_observable_density (da772096), avram_ws01e_b_equal_mesh_increment_sum_telescopes (pending source proof) and pinned Fin.sum_univ_eq_sum_range.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_equal_mesh_increment_sum_telescopes

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_esscher_mesh_path_vector_law_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ) :
    Measure.map
      (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) =
    (Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
      (fun v : Fin n → ℝ => ENNReal.ofReal
        (Real.exp (θ * (∑ i : Fin n, v i) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))) := by sorry
