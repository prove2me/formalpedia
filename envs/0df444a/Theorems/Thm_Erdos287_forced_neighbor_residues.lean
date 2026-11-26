-- Prove2me | Theorems.Thm_Erdos287_forced_neighbor_residues
-- name    : Erdos287.forced_neighbor_residues
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T02:57:30.864244+00:00
-- url     : https://prove2.me/theorems/1a6f20e6-ab64-5445-82b8-5b2d89acbc46
-- title:
--   Forced neighbors constrain the upper valuation residues
-- statement:
--   Let $1<n_0<\cdots<n_{k-1}=M$ be integers with $k\ge2$ and $\sum_i 1/n_i=1$. Fix a prime $p$, a range of valuations $1\le b\le a$, and an allowed set $C$ covering every denominator with valuation at least $b$. Assume all elements of $C$ have valuation at most $a$, and choose $L$ divisible by each $p$-free cofactor in $C$. Let $H$ be a set of certified absent integers. Form a set $F$ using positions of valuation at least $b$ in $[n_0,M]$ that are endpoints or are adjacent to a member of $H$ in the same interval.
--
--   Write $w(n)=(L/(n/p^{v_p(n)}))p^{a-v_p(n)}$. If no $T$ with $F\subseteq T\subseteq C$ satisfies $p^{a+1-b}\mid\sum_{n\in T}w(n)$, then some adjacent denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Combines consecutive omissions with the congruence across upper valuation layers.

import Mathlib

theorem Erdos287.forced_neighbor_residues (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p b a L : ℕ) (hp : Nat.Prime p) (hb : 1 ≤ b) (hba : b ≤ a)
    (C H F : Finset ℕ)
    (hC : ∀ n ∈ C, padicValNat p n ≤ a ∧ n / p ^ padicValNat p n ∣ L)
    (hfit : ∀ i, i < k → b ≤ padicValNat p (f i) → f i ∈ C)
    (hmiss : ∀ i, i < k → f i ∉ H)
    (hF : ∀ n ∈ F, f 0 ≤ n ∧ n ≤ f (k - 1) ∧ b ≤ padicValNat p n ∧
      (n = f 0 ∨ n = f (k - 1) ∨ ∃ x ∈ H, f 0 ≤ x ∧ x ≤ f (k - 1) ∧ (x + 1 = n ∨ n + 1 = x)))
    (hcert : ∀ T ⊆ C, F ⊆ T →
      ¬ p ^ (a + 1 - b) ∣ ∑ n ∈ T, (L / (n / p ^ padicValNat p n)) * p ^ (a - padicValNat p n)) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
