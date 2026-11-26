-- Prove2me | Theorems.Thm_Erdos287_upper_valuation_residue
-- name    : Erdos287.upper_valuation_residue
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T02:56:32.42668+00:00
-- url     : https://prove2.me/theorems/8c13515b-6c1d-564b-b98f-04f005f029ec
-- title:
--   A congruence across the upper valuation layers of a reciprocal sum
-- statement:
--   Suppose a finite list of positive integers $n_i$ satisfies $\sum_i 1/n_i=1$. Fix a prime $p$, write $v_i=v_p(n_i)$ and $c_i=n_i/p^{v_i}$, and fix integers $1\le b\le a$ such that $v_i\le a$ for all $i$. Let $L$ be a common multiple of the cofactors $c_i$ of the denominators with $v_i\ge b$. Then
--
--   $$
--   p^{a+1-b}\;\Bigm|\;\sum_{v_i\ge b}\frac{L}{c_i}p^{a-v_i}.
--   $$
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The congruence across arbitrary layers extends the leading-layer argument. For related two-adic identities see the Erdős 287 Lean development https://github.com/Zed-Rez/erdos-287-lean.

import Mathlib

theorem Erdos287.upper_valuation_residue (k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, i < k → 0 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) (p b a L : ℕ)
    (hp : Nat.Prime p) (hb : 1 ≤ b) (hba : b ≤ a)
    (hmax : ∀ i, i < k → padicValNat p (f i) ≤ a)
    (hL : ∀ i, i < k → b ≤ padicValNat p (f i) → f i / p ^ padicValNat p (f i) ∣ L) :
    p ^ (a + 1 - b) ∣ ∑ i ∈ (Finset.range k).filter (fun i => b ≤ padicValNat p (f i)),
      (L / (f i / p ^ padicValNat p (f i))) * p ^ (a - padicValNat p (f i)) := by sorry
