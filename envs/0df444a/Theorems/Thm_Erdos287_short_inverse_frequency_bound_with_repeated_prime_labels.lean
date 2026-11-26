-- Prove2me | Theorems.Thm_Erdos287_short_inverse_frequency_bound_with_repeated_prime_labels
-- name    : Erdos287.short_inverse_frequency_bound_with_repeated_prime_labels
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:19:56.756979+00:00
-- url     : https://prove2.me/theorems/1d272b60-2ce0-5bed-9583-75256db339ad
-- title:
--   Short inverse frequency bound when large prime labels repeat
-- statement:
--   Suppose $D$ is a finite set of positive integers at most $M$, each labeled by a prime factor at least $Y\ge2$. Let $0<a<q$. Suppose for every $n\in D$ there is a natural number $r\le R$ such that $nr\equiv a$ or $-a\pmod q$. If $(\lfloor MR/q\rfloor+1)q<Y^{K+1}$, then $|D|\le2(\lfloor MR/q\rfloor+1)K\lfloor M/Y\rfloor$. The same label may be used at several integers.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.short_inverse_frequency_bound_with_repeated_prime_labels (D : Finset ℕ) (label : ℕ → ℕ) (M q a R Y K : ℕ)
    (ha : 0 < a) (haq : a < q) (hY : 2 ≤ Y)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M ∧ (label n).Prime ∧ Y ≤ label n ∧ label n ∣ n)
    (hphase : ∀ n ∈ D, ∃ r ≤ R, n * r ≡ a [MOD q] ∨ n * r ≡ q - a [MOD q])
    (hsize : (M * R / q + 1) * q < Y ^ (K + 1)) :
    D.card ≤ 2 * (M * R / q + 1) * K * (M / Y) := by sorry
