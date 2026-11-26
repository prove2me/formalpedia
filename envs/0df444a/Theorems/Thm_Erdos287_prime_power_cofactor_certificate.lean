-- Prove2me | Theorems.Thm_Erdos287_prime_power_cofactor_certificate
-- name    : Erdos287.prime_power_cofactor_certificate
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T02:48:31.704626+00:00
-- url     : https://prove2.me/theorems/79ed473e-be51-4ac3-b5f3-d88832f8eba0
-- title:
--   Prime-power exclusion by cofactor subset residues
-- statement:
--   Let $f(0),\ldots,f(k-1)$ be strictly increasing integers greater than one whose reciprocals sum to one. Fix a prime $p$, an exponent $a\ge1$, and a finite set $C$ of positive integers coprime to $p$. Assume each denominator divisible by $p^a$ has its quotient by $p^a$ in $C$. Put $L=\operatorname{lcm}(C)$. If every nonempty subset $T\subseteq C$ satisfies $p\nmid\sum_{c\in T}L/c$, then no denominator is divisible by $p^a$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. A cofactor-set version of the leading-layer exclusion method. Related bounded-window prime-power exclusions appear at https://github.com/RexHannes/erdos-287-proof-search/blob/main/reviews/formal/TRUSTED_BANK_AUDIT.md.

import Mathlib

theorem Erdos287.prime_power_cofactor_certificate (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p e : ℕ) (hp : Nat.Prime p) (he : 1 ≤ e) (C : Finset ℕ)
    (hC : ∀ c ∈ C, 0 < c ∧ ¬ p ∣ c)
    (hfits : ∀ i, i < k → p ^ e ∣ f i → f i / p ^ e ∈ C)
    (hcert : ∀ T ⊆ C, T.Nonempty → ¬ p ∣ ∑ c ∈ T, C.lcm id / c) :
    ∀ i, i < k → ¬ p ^ e ∣ f i := by sorry
