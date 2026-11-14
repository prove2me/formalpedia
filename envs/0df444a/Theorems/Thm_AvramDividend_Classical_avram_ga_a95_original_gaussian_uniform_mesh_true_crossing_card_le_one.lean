-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one
-- name    : AvramDividend.Classical.avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:31:15.592207+00:00
-- url     : https://prove2.me/theorems/b941d2eb-39b7-4328-8273-a69390be229f
-- title:
--   At most one original Gaussian physical grid cell in the actual stopped crossing index set
-- statement:
--   For the genuine original source uniform physical Gaussian grid, the set of finite mesh indices whose cell starts strictly before the true stop and ends at or after it has at most one element, regardless of the realised stopping clock.
-- source:
--   Direct b0d9951c physical Gaussian stopping-crossing uniqueness finite-set cardinality, using ga_a91, ga_a94.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one (n m : ℕ) (ρ : ℝ≥0) :
    ((Finset.range m).filter (fun (i : ℕ) =>
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ∧
      ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))).card ≤ 1 := by sorry
