-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB292_localized_hit_open_good_bad_boundary_partition
-- name    : AvramDividend.Classical.avram_gbB292_localized_hit_open_good_bad_boundary_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:11:40.022212+00:00
-- url     : https://prove2.me/theorems/50798204-4803-4895-a645-04fd4ce4426f
-- title:
--   Every localised mesh level hit lies in a good cell, bad cell or boundary
-- statement:
--   For any sample-time level field and finite real dividend grid, a level hit before the finite horizon under a terminal variation localisation is covered by a finite mesh endpoint, a bad-increment open cell or a good-increment open cell. The partition follows the Proved B287 strict mesh covering and a threshold dichotomy, preserving the exact sample and time. This is the event-level bridge required for the B276b fixed-level Gaussian occupation assembly.

import Mathlib
open Set Finset
noncomputable section

theorem AvramDividend.Classical.avram_gbB292_localized_hit_open_good_bad_boundary_partition
    {Ω : Type*} (R : Ω → ℝ → ℝ) (d : Ω → ℕ → ℝ) (b : ℝ)
    (N : ℕ) (δ ε T M : ℝ) (hδ : 0 < δ)
    (hT : T = (N : ℝ) * δ) :
    {z : Ω × ℝ | 0 < z.2 ∧ z.2 < T ∧
      R z.1 z.2 = b ∧ d z.1 N - d z.1 0 ≤ M} ⊆
    {z : Ω × ℝ | z.2 ∈ Set.range (fun i : Fin N => (i : ℝ) * δ)} ∪
      ({z : Ω × ℝ | ∃ i : ℕ, i < N ∧
        z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
        ε < d z.1 (i + 1) - d z.1 i ∧
        R z.1 z.2 = b ∧ d z.1 N - d z.1 0 ≤ M} ∪
      ⋃ i ∈ Finset.range N, {z : Ω × ℝ |
        z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
        d z.1 (i + 1) - d z.1 i ≤ ε ∧
        R z.1 z.2 = b ∧ d z.1 N - d z.1 0 ≤ M}) := by sorry
