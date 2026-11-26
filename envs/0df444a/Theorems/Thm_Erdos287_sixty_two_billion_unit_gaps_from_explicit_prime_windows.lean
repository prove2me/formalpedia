-- Prove2me | Theorems.Thm_Erdos287_sixty_two_billion_unit_gaps_from_explicit_prime_windows
-- name    : Erdos287.sixty_two_billion_unit_gaps_from_explicit_prime_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:13:31.007901+00:00
-- url     : https://prove2.me/theorems/193e889c-16af-47ff-9fb9-3da2e52ec56b
-- title:
--   Explicit prime windows force at least 62 billion unit gaps
-- statement:
--   Let $1<n_0<\dots<n_{k-1}=M$ have reciprocal sum one, with all gaps at most two and $M\ge 62\,250\,000\,000\,000$. Put $K=250\,000\,000\,000$. Suppose for every integer $x\in[3M/4,M]$ and $d\in\{1,2\}$ there is a prime $p$ with $x\le dp$ and $K(dp-x)\le x$. Then at least $62\,000\,000\,000$ consecutive gaps are equal to one.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Explicit prime interval application of Cully-Hugill and Lee, https://arxiv.org/abs/2103.05986.

import Mathlib

theorem Erdos287.sixty_two_billion_unit_gaps_from_explicit_prime_windows (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hM : 62250000000000 ≤ f (k - 1))
    (hprime : ∀ x d : ℕ, 3 * f (k - 1) ≤ 4 * x → x ≤ f (k - 1) →
      1 ≤ d → d ≤ 2 → ∃ p : ℕ, p.Prime ∧ x ≤ d * p ∧
        (d * p - x) * 250000000000 ≤ x) :
    62000000000 ≤ ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by sorry
