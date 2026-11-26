-- Prove2me | Theorems.Thm_Erdos287_lcm_support_from_consecutive_large_factor_pairs
-- name    : Erdos287.lcm_support_from_consecutive_large_factor_pairs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:53:10.543779+00:00
-- url     : https://prove2.me/theorems/5bcb550c-14aa-4f95-b44e-02378a57f04c
-- title:
--   Least common multiple forced by consecutive large-factor pairs
-- statement:
--   Let $D\subseteq[1,M]$, and let $S$ be a finite set of starts of consecutive pairs, each hit by $D$. Suppose that both endpoints of each pair have a prime factor at least $Y>0$. Let $P$ be the primes at least $Y$ and at most $M$ dividing $L=\operatorname{lcm}(D)$. Then $|S|\le2|P|\lfloor M/Y\rfloor$ and $Y^{|P|}\le L$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Analytic application of The joint Dickman law for consecutive integers, Theorem 1.1, https://github.com/openai/math/blob/main/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf.

import Mathlib

theorem Erdos287.lcm_support_from_consecutive_large_factor_pairs (D S : Finset ℕ) (M Y : ℕ) (hY : 0 < Y)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M)
    (hcover : ∀ x ∈ S, x ∈ D ∨ x + 1 ∈ D)
    (hlabels : ∀ x ∈ S, ∀ n, n = x ∨ n = x + 1 →
      ∃ p : ℕ, p.Prime ∧ Y ≤ p ∧ p ∣ n) :
    let P := (Finset.Icc Y M).filter fun p => p.Prime ∧ p ∣ D.lcm id
    S.card ≤ 2 * P.card * (M / Y) ∧ Y ^ P.card ≤ D.lcm id := by sorry
