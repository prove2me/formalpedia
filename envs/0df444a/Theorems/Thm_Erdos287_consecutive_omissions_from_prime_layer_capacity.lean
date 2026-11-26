-- Prove2me | Theorems.Thm_Erdos287_consecutive_omissions_from_prime_layer_capacity
-- name    : Erdos287.consecutive_omissions_from_prime_layer_capacity
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:23:37.81958+00:00
-- url     : https://prove2.me/theorems/559a61ab-8cda-5396-ae1a-1eca3e58d617
-- title:
--   Too many disjoint adjacent pairs exhaust the capacity of usable prime layers
-- statement:
--   Let $D$ be distinct positive denominators at most $M$ whose reciprocal sum is one. Take a collection $S$ of pairwise disjoint adjacent pairs in $[m,M]$, with both endpoints of each pair divisible by a prime from one of finitely many groups. For group $i$, primes are at least $Y_i$ and do not divide $L_i$. The cofactor support $U_i$ consists of positive divisors of $L_i$. The family $F_i$ consists of nonempty subsets of $U_i$, and $|U_i|L_i<Y_i^{K_i+1}$. For every group prime dividing some member of $D$, suppose its highest layer has positive exponent, its cofactors lie in $U_i$, and its cleared numerator equals the cleared numerator of some member of $F_i$. If $|S|>\sum_i\lfloor M/Y_i\rfloor |F_i|K_i$, two consecutive integers in $[m,M]$ are missing from $D$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Capacity for all adjacent pairs after allowing exceptional highest layers.

import Mathlib

theorem Erdos287.consecutive_omissions_from_prime_layer_capacity (D S J : Finset ℕ) (m M : ℕ)
    (P U : ℕ → Finset ℕ) (F : ℕ → Finset (Finset ℕ)) (L Y K : ℕ → ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hends : ∀ x ∈ S, m ≤ x ∧ x + 1 ≤ M)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + 1 < y ∨ y + 1 < x)
    (hlabels : ∀ x ∈ S, ∀ n : ℕ, (n = x ∨ n = x + 1) →
      ∃ i ∈ J, ∃ p ∈ P i, p ∣ n)
    (hgroups : ∀ i ∈ J, 0 < L i ∧ 2 ≤ Y i ∧
      (∀ b ∈ U i, 0 < b ∧ b ∣ L i) ∧
      (∀ T ∈ F i, T ⊆ U i ∧ T.Nonempty) ∧
      (∀ p ∈ P i, p.Prime ∧ Y i ≤ p ∧ ¬ p ∣ L i) ∧
      (U i).card * L i < Y i ^ (K i + 1))
    (hconfig : ∀ i ∈ J, ∀ p ∈ P i, (∃ n ∈ D, p ∣ n) → ∃ e : ℕ, 1 ≤ e ∧
      (∀ n ∈ D, padicValNat p n ≤ e) ∧
      (∀ n ∈ D, padicValNat p n = e → n / p ^ e ∈ U i) ∧
      ∃ T ∈ F i, (∑ b ∈ T, L i / b) =
        ∑ n ∈ D.filter (fun n => padicValNat p n = e), L i / (n / p ^ e))
    (hmany : (∑ i ∈ J, (M / Y i) * ((F i).card * K i)) < S.card) :
    ∃ x, m ≤ x ∧ x + 1 ≤ M ∧ x ∉ D ∧ x + 1 ∉ D := by sorry
