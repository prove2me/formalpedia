-- Prove2me | Theorems.Thm_Erdos287_short_inverse_frequencies_have_few_large_prime_labels
-- name    : Erdos287.short_inverse_frequencies_have_few_large_prime_labels
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:04:45.657799+00:00
-- url     : https://prove2.me/theorems/faaf7447-8dac-43cc-8d3c-936af3122ff5
-- title:
--   Counting short-arc reciprocal frequencies by distinct large prime factors
-- statement:
--   Let $D$ be a finite set of integers $n\le M$ with distinct associated prime divisors $r_n\ge Y\ge2$, and let $1\le a<q$. If for every $n\in D$ there is a $b\le R$ with $nb\equiv a$ or $nb\equiv q-a\pmod q$, and $(\lfloor MR/q\rfloor+1)q<Y^{K+1}$, then $|D|\le2(\lfloor MR/q\rfloor+1)K$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.short_inverse_frequencies_have_few_large_prime_labels (D : Finset ℕ) (label : ℕ → ℕ) (M q a R Y K : ℕ)
    (ha : 0 < a) (haq : a < q) (hY : 2 ≤ Y)
    (hD : ∀ n ∈ D, n ≤ M ∧ (label n).Prime ∧ Y ≤ label n ∧ label n ∣ n)
    (hinj : Set.InjOn label (↑D : Set ℕ))
    (hphase : ∀ n ∈ D, ∃ r ≤ R, n * r ≡ a [MOD q] ∨ n * r ≡ q - a [MOD q])
    (hsize : (M * R / q + 1) * q < Y ^ (K + 1)) :
    D.card ≤ 2 * (M * R / q + 1) * K := by sorry
