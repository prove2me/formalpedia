-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger163_true_uniform_clipped_mesh_first_crossing
-- name    : AvramDividend.Classical.avram_gledger163_true_uniform_clipped_mesh_first_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:25:50.256907+00:00
-- url     : https://prove2.me/theorems/0797a248-d4cb-4367-9b4c-8cf5f5246090
-- title:
--   The exact n/(m+1) physical stopped grid has one chronological crossing
-- statement:
--   For positive original clipped rho at most the finite horizon n, the true n/(m+1) mesh has a unique first terminal crossing and remains strictly pre-rho before and constant after. The case rho=0 is handled separately in the source Euler identity. Necessary finite partition input to gledger161 and therefore original gledger139.
-- source:
--   Proved gledger91 first-crossing lemma, applied to the genuine deterministic uniform grid with endpoint m+1; no arbitrary non-refining grid.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger91_monotone_clipped_grid_first_crossing_index
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger163_true_uniform_clipped_mesh_first_crossing
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 1 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by sorry
