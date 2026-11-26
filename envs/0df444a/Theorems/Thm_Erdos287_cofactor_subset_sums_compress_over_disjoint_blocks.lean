-- Prove2me | Theorems.Thm_Erdos287_cofactor_subset_sums_compress_over_disjoint_blocks
-- name    : Erdos287.cofactor_subset_sums_compress_over_disjoint_blocks
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:30:56.956448+00:00
-- url     : https://prove2.me/theorems/2d4e8601-6df0-4c81-b336-fe0a03d7fe30
-- title:
--   Disjoint cofactor blocks combine their subset-sum compression multiplicatively
-- statement:
--   Let $U$ be finite and carry positive integer weights. Let $B_i$ be pairwise disjoint subsets of $U$. For each block, suppose the family $A_i$ contains a subset with each weight sum attainable within $B_i$. Then all nonempty subset sums of $U$ have representatives in a family of at most $2^{|U\setminus\bigcup_i B_i|}\prod_i |A_i|$ nonempty subsets of $U$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Independent compression of cleared cofactor sums on disjoint blocks.

import Mathlib

theorem Erdos287.cofactor_subset_sums_compress_over_disjoint_blocks (U I : Finset ℕ) (B : ℕ → Finset ℕ) (A : ℕ → Finset (Finset ℕ)) (w : ℕ → ℕ)
    (hpos : ∀ x ∈ U, 0 < w x)
    (hB : ∀ i ∈ I, B i ⊆ U)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (hA : ∀ i ∈ I, ∀ V ∈ A i, V ⊆ B i)
    (hlocal : ∀ i ∈ I, ∀ T ⊆ B i, ∃ V ∈ A i, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) :
    ∃ F : Finset (Finset ℕ),
      (∀ V ∈ F, V ⊆ U ∧ V.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ 2 ^ (U \ I.biUnion B).card * ∏ i ∈ I, (A i).card := by sorry
