-- Prove2me | Theorems.Thm_Erdos287_exclusive_one_parity_repairs_preserve_layer_patterns
-- name    : Erdos287.exclusive_one_parity_repairs_preserve_layer_patterns
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:23:57.992936+00:00
-- url     : https://prove2.me/theorems/fd790ffa-c698-4329-afb5-b81b1ab090c8
-- title:
--   Exclusive one-parity repairs preserve each tested layer
-- statement:
--   Let $H$ be an initially omitted subset of the finite integer-position set $I$, with no consecutive positions. For every label $p$ in a finite test set $P$, let $T_p\subseteq I$ consist of odd positions with no neighbor in $H$. Suppose any tested label $q$ dividing a position of $T_p$ equals $p$. Let $O=H\cup\bigcup_{p\in P}T_p$. Then $O$ is an omitted subset of $I$ containing $H$, no two elements of $O$ are consecutive, and the retained multiples of each $p\in P$ are exactly its multiples in $I$ outside $H\cup T_p$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.exclusive_one_parity_repairs_preserve_layer_patterns (I H P : Finset ℕ) (T : ℕ → Finset ℕ)
    (hH : H ⊆ I) (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hT : ∀ p ∈ P, ∀ n ∈ T p, n ∈ I ∧ Odd n ∧ n - 1 ∉ H ∧ n + 1 ∉ H)
    (hexclusive : ∀ p ∈ P, ∀ n ∈ T p, ∀ q ∈ P, q ∣ n → p = q) :
    let O := H ∪ P.biUnion T
    H ⊆ O ∧ O ⊆ I ∧ (∀ n ∈ O, n + 1 ∉ O) ∧
      ∀ p ∈ P, (I \ O).filter (fun n => p ∣ n) =
        I.filter (fun n => p ∣ n) \ (H ∪ T p) := by sorry
