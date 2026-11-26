-- Prove2me | Theorems.Thm_Erdos287_uniform_exceptional_primes_for_bounded_cofactors
-- name    : Erdos287.uniform_exceptional_primes_for_bounded_cofactors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:00:26.598409+00:00
-- url     : https://prove2.me/theorems/e3ce6b75-07c7-5e29-b7bf-66fd0ca22a32
-- title:
--   One exceptional prime set controls every denominator sequence with the same cofactor bound
-- statement:
--   Let $L=\operatorname{lcm}(1,\ldots,B)$, let $Y\ge2$ and $B<Y$, and suppose $BL<Y^{K+1}$. For every $Z$ and $H$ there is a set $E$ of primes in $[Y,H]$ of size at most
--   $$
--   K(B+1)\prod_{p\mid L,\ p\ \mathrm{prime}}
--   \begin{cases}p^{v_p(L)}&p\le Z\\2^{\lfloor B/p\rfloor}&p>Z.\end{cases}
--   $$
--   The same $E$ works for all distinct increasing denominator sequences greater than one with reciprocal sum one and maximum $M\le H$. For any prime $p\ge Y$ outside $E$ and any exponent $e\ge1$ with $M<(B+1)p^e$, no denominator is divisible by $p^e$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Uniform finite prime exclusions using compressed cofactor numerators.

import Mathlib

theorem Erdos287.uniform_exceptional_primes_for_bounded_cofactors (B Z Y H K : ℕ) (hY : 2 ≤ Y) (hBY : B < Y)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1)) :
    let L := (Finset.Icc 1 B).lcm id
    ∃ E : Finset ℕ, E ⊆ Finset.Icc Y H ∧ (∀ p ∈ E, p.Prime) ∧
      E.card ≤ ((B + 1) * ∏ p ∈ L.primeFactors,
        if p ≤ Z then p ^ L.factorization p else 2 ^ (B / p)) * K ∧
      ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
        (∀ i < k, 1 < f i) → (∀ i j, i < j → j < k → f i < f j) →
        (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) → f (k - 1) ≤ H →
        ∀ p e : ℕ, p.Prime → Y ≤ p → 1 ≤ e → p ∉ E →
          f (k - 1) < (B + 1) * p ^ e → ∀ i < k, ¬ p ^ e ∣ f i := by sorry
