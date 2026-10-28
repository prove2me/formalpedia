-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_terminal
-- name    : AvramDividend.Classical.avram_ws01e_b_fin_mesh_increment_sum_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:53:16.64038+00:00
-- url     : https://prove2.me/theorems/fd442ab6-79cf-4b9b-a1cb-63e197a257b8
-- title:
--   Fin-indexed equal-mesh Lévy increment vector sums to terminal displacement
-- statement:
--   For every spectrally negative Lévy process, mesh δ, dimension n and path ω, the sum of the n increments in the Fin n-indexed sample vector exactly equals X_(nδ)(ω)−X_0(ω). This translates the already-Proved range-indexed telescoping lemma to the actual Fin n coordinate vector and is the source-faithful equality needed to equate the true finite-terminal Esscher density and the vector-sum density.
-- source:
--   Accepted avram_ws01e_b_equal_mesh_increment_sum_telescopes (24166a47) and pinned Mathlib Fin.sum_univ_eq_sum_range.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_equal_mesh_increment_sum_telescopes

open AvramDividend.Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_fin_mesh_increment_sum_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n,
      (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
       X.X ((i.val : ℝ≥0) * δ) ω)) =
    X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω := by sorry
