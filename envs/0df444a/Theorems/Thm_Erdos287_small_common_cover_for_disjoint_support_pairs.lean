-- Prove2me | Theorems.Thm_Erdos287_small_common_cover_for_disjoint_support_pairs
-- name    : Erdos287.small_common_cover_for_disjoint_support_pairs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:48:13.860192+00:00
-- url     : https://prove2.me/theorems/eadbda5e-c0fb-502a-b301-975ee3da0d36
-- title:
--   Small common cover for disjoint prime supports
-- statement:
--   Let the finite family I have pairs of disjoint subsets A(i), B(i) of a finite universe U, with |A(i)|+|B(i)| at most k and k at most |U|. If |I|(2^k-1)^t < (2^k)^t, then there are t subsets of U such that every pair has a subset containing A(i) and disjoint from B(i).
-- source:
--   Erdős #287, short Type II cross-coprimality in Fouvry §III.7.

import Mathlib

theorem Erdos287.small_common_cover_for_disjoint_support_pairs {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (A B : ι → Finset α) (k t : ℕ)
    (hk : k ≤ U.card)
    (hpair : ∀ i ∈ I, A i ⊆ U ∧ B i ⊆ U ∧ Disjoint (A i) (B i) ∧
      (A i).card + (B i).card ≤ k)
    (hcount : I.card * (2 ^ k - 1) ^ t < (2 ^ k) ^ t) :
    ∃ f : Fin t → Finset α, (∀ j, f j ⊆ U) ∧
      ∀ i ∈ I, ∃ j, A i ⊆ f j ∧ Disjoint (B i) (f j) := by sorry
