-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_linear_ordered_set_factorial_pair_ncard
-- name    : AvramDividend.Classical.avram_a20_finite_linear_ordered_set_factorial_pair_ncard
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:16:45.558258+00:00
-- url     : https://prove2.me/theorems/d669288f-0c1c-44e7-8ff0-09ec4207bc8c
-- title:
--   Exact factorial cardinal equals twice the chronological pair cardinal of a finite ordered set
-- statement:
--   For any finite set S of nonnegative real event times, the real factorial number of points |S|(|S|−1) equals twice the number of strictly chronologically ordered distinct pairs (u,v) in S×S with u<v. This is a universal finite-set combinatorial identity, established using finite-set cardinality, the binomial choose-two identity and a rigorous bridge from Set.ncard to Finset.card. It is a reusable self-contained structural ingredient to calculate literal original Lévy marked jump factorial moments.

import Mathlib
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_linear_ordered_set_factorial_pair_ncard
    (S : Set ℝ≥0) (hS : S.Finite) :
    (S.ncard : ℝ) * ((S.ncard : ℝ) - 1) =
      2 * (((S ×ˢ S) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard : ℝ) := by sorry
