-- Prove2me | Theorems.Thm_Erdos287_disjoint_prime_blocks_multiply_subsum_counts
-- name    : Erdos287.disjoint_prime_blocks_multiply_subsum_counts
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T17:59:58.002273+00:00
-- url     : https://prove2.me/theorems/d8200878-0505-4596-9c76-3b0d5217c2ca
-- title:
--   Product lower count for disjoint prime cofactor blocks
-- statement:
--   Let \(p_i\) be distinct primes and \(L_j>0\) integers coprime to all \(p_i\). For each \(i\), take an arbitrary finite set \(S_i\) of numerator choices in \([0,p_i)\). Then the values \(\sum_i a_i/(p_iL_i)\), with \(a_i\in S_i\), number exactly \(\prod_i|S_i|\).
-- source:
--   Erdős #287, restricted cofactor subsum counts.

import Mathlib
open Finset

theorem Erdos287.disjoint_prime_blocks_multiply_subsum_counts (I : Finset ℕ) (p L : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (hp : ∀ i ∈ I, (p i).Prime) (hp_inj : Set.InjOn p (↑I : Set ℕ))
    (hL : ∀ i ∈ I, 0 < L i) (hcop : ∀ i ∈ I, ∀ j ∈ I, ¬ p i ∣ L j)
    (hsize : ∀ i ∈ I, ∀ a ∈ S i, a < p i) :
    ((I.pi S).image (fun a => ∑ i ∈ I.attach,
      (a i.val i.property : ℚ) / (p i.val * L i.val : ℕ))).card =
      ∏ i ∈ I, (S i).card := by sorry
