-- Prove2me | Theorems.Thm_Erdos287_short_cofactor_cycles_balance
-- name    : Erdos287.short_cofactor_cycles_balance
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:46:26.189363+00:00
-- url     : https://prove2.me/theorems/0428d4dc-b9c5-5a98-896d-e6e666b8b941
-- title:
--   Short cycles of adjacent multiples have balanced cofactor products
-- statement:
--   Let $p_0,\ldots,p_k=p_0$ be natural numbers with $k>0$, and suppose $|a_i p_i-b_i p_{i+1}|=1$ for each $i<k$, with natural cofactors $a_i,b_i\le B$. If $p_0>kB^{k-1}$, then $\prod_{i<k}a_i=\prod_{i<k}b_i$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.short_cofactor_cycles_balance (a b p : ℕ → ℕ) (k B : ℕ) (hk : 0 < k)
    (hclose : p k = p 0) (hsize : k * B ^ (k - 1) < p 0)
    (hab : ∀ i < k, a i ≤ B ∧ b i ≤ B)
    (hstep : ∀ i < k, |(a i : ℤ) * p i - (b i : ℤ) * p (i + 1)| = 1) :
    (∏ i ∈ Finset.range k, a i) = ∏ i ∈ Finset.range k, b i := by sorry
