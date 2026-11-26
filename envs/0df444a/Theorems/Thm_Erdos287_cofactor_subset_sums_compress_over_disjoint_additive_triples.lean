-- Prove2me | Theorems.Thm_Erdos287_cofactor_subset_sums_compress_over_disjoint_additive_triples
-- name    : Erdos287.cofactor_subset_sums_compress_over_disjoint_additive_triples
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:22:58.874596+00:00
-- url     : https://prove2.me/theorems/dd000df0-5ada-5243-820f-141b47615266
-- title:
--   Disjoint additive triples compress the family of cofactor subset sums
-- statement:
--   Let $U$ be a finite set of weighted positions, with nonnegative integer weights $w$. Suppose there are $r$ pairwise disjoint three-element subsets $\{a_i,b_i,c_i\}$ of $U$, with $w(a_i)=w(b_i)+w(c_i)$. There is a family $F$ of at most $7^r 2^{|U|-3r}$ nonempty subsets of $U$ such that every nonempty subset of $U$ has the same total weight as a member of $F$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Compression of cleared cofactor numerators using exact reciprocal identities.

import Mathlib

theorem Erdos287.cofactor_subset_sums_compress_over_disjoint_additive_triples (U I : Finset ℕ) (a b c w : ℕ → ℕ)
    (hblocks : ∀ i ∈ I, ({a i, b i, c i} : Finset ℕ) ⊆ U)
    (hne : ∀ i ∈ I, a i ≠ b i ∧ a i ≠ c i ∧ b i ≠ c i)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint ({a i, b i, c i} : Finset ℕ) {a j, b j, c j})
    (hweight : ∀ i ∈ I, w (a i) = w (b i) + w (c i)) :
    ∃ F : Finset (Finset ℕ),
      (∀ V ∈ F, V ⊆ U ∧ V.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ 7 ^ I.card * 2 ^ (U.card - 3 * I.card) := by sorry
