-- Prove2me | Theorems.Thm_Erdos287_cofactor_subset_sums_compress_by_coprime_residues
-- name    : Erdos287.cofactor_subset_sums_compress_by_coprime_residues
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:32:27.285828+00:00
-- url     : https://prove2.me/theorems/deda2225-3638-5098-840f-f5581fcc1496
-- title:
--   Coprime residue supports compress the possible cleared cofactor sums
-- statement:
--   Let $U$ be finite with integer weights $0\le w(x)\le L$, where $L$ is the product of pairwise coprime positive integers $q_i$. Put $s_i=|\{x\in U:q_i\nmid w(x)\}|$. Then every nonempty subset sum of $U$ has a representative in a family of at most $(|U|+1)\prod_i\min(q_i,2^{s_i})$ nonempty subsets of $U$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. See also Bleicher and Erdős, Denominators of Egyptian fractions II, https://old.renyi.hu/~p_erdos/1976-10.pdf.

import Mathlib

theorem Erdos287.cofactor_subset_sums_compress_by_coprime_residues (U I : Finset ℕ) (q w : ℕ → ℕ) (L : ℕ)
    (hL : L = ∏ i ∈ I, q i) (hq : ∀ i ∈ I, 0 < q i)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (q i).Coprime (q j))
    (hw : ∀ x ∈ U, w x ≤ L) :
    ∃ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ (U.card + 1) * ∏ i ∈ I,
        min (q i) (2 ^ (U.filter (fun x => ¬ q i ∣ w x)).card) := by sorry
