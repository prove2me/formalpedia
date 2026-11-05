-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_pair_card_sum
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_pair_card_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:36:44.717486+00:00
-- url     : https://prove2.me/theorems/208e08c0-ff4e-47b8-8650-883f5b8e4611
-- title:
--   Disjoint physical future uniform cells convert chronological-pair cover to an exact finite grid sum
-- statement:
--   For a finite set of original physical times, a specified cover of its chronological time pairs by uniform past-future fibres and pairwise disjointness of the future half-open cells imply that the chronological pair count equals the sum of the grid fibre counts.
-- source:
--   Pinned Finset.card_biUnion and literal physical-time grid crossing pairs; bridge to the accepted original negative-band jump count decomposition and Fatou factorial moment route.

import Mathlib

open Set
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_pair_card_sum
    (F : Finset ℝ≥0) (δ : ℝ≥0) (m : ℕ)
    (hcover :
      (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2) =
        (Finset.univ : Finset (Fin m)).biUnion (fun i =>
          (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
            p.1 ≤ (i.val : ℝ≥0) * δ ∧
            (i.val : ℝ≥0) * δ < p.2 ∧
            p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))))
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint
        (Ioc ((i.val : ℝ≥0) * δ) (((i.val + 1 : ℕ) : ℝ≥0) * δ))
        (Ioc ((j.val : ℝ≥0) * δ) (((j.val + 1 : ℕ) : ℝ≥0) * δ))) :
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
      ∑ i : Fin m,
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
          p.1 ≤ (i.val : ℝ≥0) * δ ∧
          (i.val : ℝ≥0) * δ < p.2 ∧
          p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))).card := by sorry
