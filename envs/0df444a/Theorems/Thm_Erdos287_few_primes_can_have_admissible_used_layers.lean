-- Prove2me | Theorems.Thm_Erdos287_few_primes_can_have_admissible_used_layers
-- name    : Erdos287.few_primes_can_have_admissible_used_layers
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:09:24.53363+00:00
-- url     : https://prove2.me/theorems/75be79dd-bf1c-4b8a-8e68-0e45871b6a2c
-- title:
--   Few primes can use a highest layer from a common cofactor family
-- statement:
--   Fix a finite cofactor universe $U$ of positive divisors of $L>0$ and a family $F$ of its nonempty subsets. Let $P$ be a finite set of primes $p\ge Y\ge2$ not dividing $L$. For each $p\in P$, suppose there is a reciprocal sum of one over distinct positive denominators such that all $p$-valuations are at most a positive $e$, and the cofactors of its exact valuation-$e$ layer form a member of $F$. The denominator set and $e$ may depend on $p$. If $|U|L<Y^{K+1}$, then $|P|\le K|F|$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Finite exceptional-prime bound applied directly to actual highest valuation layers.

import Mathlib

theorem Erdos287.few_primes_can_have_admissible_used_layers (U P : Finset ℕ) (F : Finset (Finset ℕ)) (L Y K : ℕ)
    (hL : 0 < L) (hY : 2 ≤ Y) (hU : ∀ n ∈ U, 0 < n ∧ n ∣ L)
    (hF : ∀ T ∈ F, T ⊆ U ∧ T.Nonempty)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ ¬ p ∣ L)
    (hbound : U.card * L < Y ^ (K + 1))
    (hconfig : ∀ p ∈ P, ∃ (D : Finset ℕ) (e : ℕ), 1 ≤ e ∧
      (∀ n ∈ D, 0 < n ∧ padicValNat p n ≤ e) ∧
      (∑ n ∈ D, (1 : ℚ) / n) = 1 ∧
      (D.filter (fun n => padicValNat p n = e)).image (fun n => n / p ^ e) ∈ F) :
    P.card ≤ F.card * K := by sorry
