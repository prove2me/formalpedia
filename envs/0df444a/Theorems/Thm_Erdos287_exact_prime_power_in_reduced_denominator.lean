-- Prove2me | Theorems.Thm_Erdos287_exact_prime_power_in_reduced_denominator
-- name    : Erdos287.exact_prime_power_in_reduced_denominator
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:14:19.593803+00:00
-- url     : https://prove2.me/theorems/0157d832-2bab-4236-bba2-8532957b73c1
-- title:
--   The leading prime-power residue determines the reduced reciprocal denominator
-- statement:
--   Let $D$ be a finite set of positive denominators with integer weights $w(n)$, and let $p$ be prime. Fix $e\ge1$ such that $v_p(n)\le e$ for all $n\in D$. Choose a common multiple $L$ of all $n/p^e$ with $v_p(n)=e$, with $p\nmid L$. The $p$-valuation of the reduced denominator of $\sum_{n\in D}w(n)/n$ is exactly $e$ if and only if
--
--   $$p\nmid \sum_{\substack{n\in D\\v_p(n)=e}} w(n)\frac L{n/p^e}.$$
--
--   In particular, this criterion applies to the signed difference of two candidate reciprocal sums.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The leading valuation test for arbitrary weighted reciprocal sums.

import Mathlib

theorem Erdos287.exact_prime_power_in_reduced_denominator (D : Finset ℕ) (w : ℕ → ℤ) (p e L : ℕ)
    (hp : p.Prime) (he : 1 ≤ e) (hL : ¬ p ∣ L)
    (hpos : ∀ n ∈ D, 0 < n) (hmax : ∀ n ∈ D, padicValNat p n ≤ e)
    (hcof : ∀ n ∈ D, padicValNat p n = e → n / p ^ e ∣ L) :
    padicValNat p (∑ n ∈ D, (w n : ℚ) / n).den = e ↔
      ¬ (p : ℤ) ∣ ∑ n ∈ D.filter (fun n => padicValNat p n = e),
        w n * ((L / (n / p ^ e) : ℕ) : ℤ) := by sorry
