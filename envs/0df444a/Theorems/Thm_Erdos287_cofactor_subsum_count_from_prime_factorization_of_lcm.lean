-- Prove2me | Theorems.Thm_Erdos287_cofactor_subsum_count_from_prime_factorization_of_lcm
-- name    : Erdos287.cofactor_subsum_count_from_prime_factorization_of_lcm
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:36:32.196051+00:00
-- url     : https://prove2.me/theorems/bc7aedb0-6db7-4933-98c2-f34c652dcade
-- title:
--   Prime factorization of the cofactor LCM bounds its distinct cleared subsums
-- statement:
--   Set $U=\{1,\ldots,B\}$ and $L=\operatorname{lcm}(U)$. Fix a splitting point $Z$. All nonempty subset sums of weights $L/x$ for $x\in U$ have representatives in at most $(B+1)\prod_{p\mid L}\!c_p$ nonempty subsets, where $c_p=p^{v_p(L)}$ for $p\le Z$ and $c_p=2^{\lfloor B/p\rfloor}$ for $p>Z$. The product ranges over prime divisors.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. For reciprocal subsum estimates see Bleicher and Erdős, Denominators of Egyptian fractions II, https://old.renyi.hu/~p_erdos/1976-10.pdf.

import Mathlib

theorem Erdos287.cofactor_subsum_count_from_prime_factorization_of_lcm (B Z : ℕ) :
    let U := Finset.Icc 1 B
    let L := U.lcm id
    ∃ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, L / x) = ∑ x ∈ T, L / x) ∧
      F.card ≤ (B + 1) * ∏ p ∈ L.primeFactors,
        if p ≤ Z then p ^ L.factorization p else 2 ^ (B / p) := by sorry
