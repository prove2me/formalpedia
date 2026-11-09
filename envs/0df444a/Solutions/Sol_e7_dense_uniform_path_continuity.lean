-- Prove2me | solution 1 for e7_dense_uniform_path_continuity
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T08:03:52.746965+00:00
-- url     : https://prove2.me/submissions/cc5a3157-5eca-4f00-b5da-346788622d84

import Mathlib

open Metric Set Filter
open scoped NNReal

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Submodule ℝ V) (S : Set V)
    (q : V → ℝ≥0 → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (happrox : ∀ x : L, ∀ ε : ℝ, 0 < ε →
      ∃ y, y ∈ S ∧ ‖(x : V) - y‖ < ε)
    (herror : ∀ x : L, ∀ y, y ∈ S → ∀ t,
      ‖q x t - q y t‖ ≤ p * ‖(x : V) - y‖)
    (hcont : ∀ y, y ∈ S → Continuous (q y)) :
    ∀ x : L, Continuous (q x) := by
  intro x
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨y, hyS, hy⟩ := happrox x (ε / (4 * (p + 1))) (by positivity)
  have hp1 : 0 < p + 1 := by linarith
  have hd : ‖(x : V) - y‖ ≤ ε / (4 * (p + 1)) := le_of_lt hy
  have hpy : p * ‖(x : V) - y‖ ≤ ε / 4 := by
    calc p * ‖(x : V) - y‖ ≤ p * (ε / (4 * (p + 1))) :=
          mul_le_mul_of_nonneg_left hd hp
      _ = (p / (p + 1)) * (ε / 4) := by field_simp
      _ ≤ 1 * (ε / 4) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            rw [div_le_one hp1]
            linarith
      _ = ε / 4 := by ring
  have hcont_y : ContinuousAt (q y) t := (hcont y hyS).continuousAt
  rw [Metric.continuousAt_iff] at hcont_y
  obtain ⟨δ, hδ, hball⟩ := hcont_y (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun t' ht' => ?_⟩
  have h1 : ‖q x t' - q x t‖ ≤
      ‖q x t' - q y t'‖ + ‖q y t' - q y t‖ + ‖q y t - q x t‖ := by
    calc ‖q x t' - q x t‖ = ‖(q x t' - q y t') + (q y t' - q y t) + (q y t - q x t)‖ := by ring_nf
      _ ≤ ‖q x t' - q y t'‖ + ‖q y t' - q y t‖ + ‖q y t - q x t‖ := by
          apply norm_add_le_of_le (norm_add_le_of_le le_rfl le_rfl) le_rfl
  have h2 : ‖q x t' - q y t'‖ ≤ ε / 4 := le_trans (herror x y hyS t') hpy
  have h3 : ‖q y t - q x t‖ ≤ ε / 4 := by
    rw [norm_sub_rev]
    exact le_trans (herror x y hyS t) hpy
  have h4 : ‖q y t' - q y t‖ < ε / 2 := hball ht'
  rw [dist_eq_norm]
  linarith
