-- Prove2me | Theorems.Thm_Erdos287_safe_predecessor_pair_excludes_wider_band
-- name    : Erdos287.safe_predecessor_pair_excludes_wider_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:42:49.29426+00:00
-- url     : https://prove2.me/theorems/3acca86d-512d-467d-84d5-fc97a93222b9
-- title:
--   Safe-predecessor prime pair excludes a wider band
-- statement:
--   Let \(p,q\) be primes with \(p>137\) and \(q+1=2p\). If the largest denominator \(M\) of a strictly increasing unit-fraction representation of \(1\) satisfies \(q+1\le M\le 27q/10\), some consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Specialization of the prime-power pair band theorem.

import Mathlib

theorem Erdos287.safe_predecessor_pair_excludes_wider_band (p q k : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hlarge : 137 < p) (hrel : q + 1 = 2 * p)
    (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : q + 1 ≤ f (k - 1)) (hhi : 10 * f (k - 1) ≤ 27 * q) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
