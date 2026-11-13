-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_original_chronological_pair_ncard_eq_finset
-- name    : AvramDividend.Classical.avram_a20_finite_original_chronological_pair_ncard_eq_finset
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:15:06.948557+00:00
-- url     : https://prove2.me/theorems/67150b39-fff6-4aa1-bff1-a529231ffaeb
-- title:
--   Every finite original marked-time set has literal chronological pair ncard equal to its finite-set filter cardinal
-- statement:
--   For any finite set of nonnegative real event times, the Set.ncard of distinct strictly chronological ordered pairs equals the Finset.card of the filtered pair product of the associated finite set. This exact finite combinatorial bridge is independent of any stochastic process and converts the physical original Lévy Borel chronological pair nat-count into the verified finite uniform-grid pair-count lemmas. It uses set product and finite-set membership equivalences, then Set.ncard_coe_finset.

import Mathlib
open Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_original_chronological_pair_ncard_eq_finset
    (S : Set ℝ≥0) (hS : S.Finite) :
    ((S ×ˢ S) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard =
    ((hS.toFinset ×ˢ hS.toFinset).filter
      (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
