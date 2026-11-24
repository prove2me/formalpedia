-- Prove2me | solution 1 for rank_neg_one_iff_unwinnable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:07.751079+00:00
-- url     : https://prove2.me/submissions/4f65c011-818f-4f29-b1b6-f23356772e18

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_eff_degree_zero
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma rank_eq_neg_one_iff_unwinnable  (G : CFGraph) (D : CFDiv G) :
  rank_eq G D (-1) ↔ ¬(winnable G D) := by
  constructor
  · intro h
    rcases h with ⟨_, h_rank⟩
    contrapose! h_rank
    simp only [Int.reduceNeg, neg_add_cancel]
    intro E h_E
    rcases h_E with ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simpa only [E_zero, sub_zero] using h_rank
  · intro h_unwinnable
    refine ⟨rank_geq_neg G D (-1) (by norm_num), ?_⟩
    intro h_rank_geq
    specialize h_rank_geq 0
    apply h_unwinnable
    rw [sub_zero] at h_rank_geq
    apply h_rank_geq
    constructor
    · dsimp only [effective, Pi.zero_apply]
      norm_num
    · simp only [_root_.map_zero, Int.reduceNeg, neg_add_cancel]
private lemma rank_eq_iff (G : CFGraph) (D : CFDiv G) (r : ℤ) :
  rank_eq G D r ↔ rank G D = r := by
  dsimp only [rank_eq]
  have split_eq x: x = r ↔ (x ≥ r ∧ ¬(x ≥ r + 1)) := by
    rw [not_le]
    rw [Int.lt_add_one_iff]
    have helper := @le_antisymm_iff _ _ x r
    rw [helper, and_comm]
  rw [split_eq (rank G D)]
  rw [rank_geq_iff G D r, rank_geq_iff G D (r+1)]
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  rw [← rank_eq_iff]
  exact rank_eq_neg_one_iff_unwinnable G D
