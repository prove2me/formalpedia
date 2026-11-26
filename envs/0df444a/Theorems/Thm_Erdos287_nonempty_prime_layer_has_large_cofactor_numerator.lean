-- Prove2me | Theorems.Thm_Erdos287_nonempty_prime_layer_has_large_cofactor_numerator
-- name    : Erdos287.nonempty_prime_layer_has_large_cofactor_numerator
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:52:39.223655+00:00
-- url     : https://prove2.me/theorems/c9b4443c-c2f5-4893-8595-99125cb34c42
-- title:
--   A nonempty prime-power layer needs a cleared numerator at least as large as the prime
-- statement:
--   Let $D$ be positive distinct denominators at most $M$ with reciprocal sum one. Fix a prime $p$ and $e\ge1$ such that all denominators have $p$-valuation at most $e$. Suppose the exact valuation-$e$ layer is nonempty and has $t$ terms, with cofactors $c_1,\dots,c_t$. Set $A=\sum_{i=1}^t\prod_{j\ne i}c_j$ and $B=\lfloor M/p^e\rfloor$. Then $p\mid A$ and $p\le A\le t B^{t-1}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. A size-sensitive constraint on the top valuation layer.

import Mathlib

theorem Erdos287.nonempty_prime_layer_has_large_cofactor_numerator (D : Finset ℕ) (M p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M) (hmax : ∀ n ∈ D, padicValNat p n ≤ e)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hT : (D.filter (fun n => padicValNat p n = e)).Nonempty) :
    let T := D.filter (fun n => padicValNat p n = e)
    let A := ∑ n ∈ T, ∏ d ∈ T.erase n, d / p ^ e
    p ∣ A ∧ p ≤ A ∧ A ≤ T.card * (M / p ^ e) ^ (T.card - 1) := by sorry
