-- Prove2me | Theorems.Thm_FamousTheorems_multinomial_theorem
-- name    : FamousTheorems.multinomial_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:15.738016+00:00
-- url     : https://prove2.me/theorems/095ebe08-f1c9-48c0-a5db-58540145e1b3
-- title:
--   The multinomial theorem
-- statement:
--   **The multinomial theorem.** In a commutative semiring, for a finite index set $s$ and $n\in\mathbb N$,
--   $$\Big(\sum_{i\in s}x_i\Big)^n=\sum_{\substack{k:s\to\mathbb N\\ \sum_i k_i=n}}\binom{n}{(k_i)_{i\in s}}\prod_{i\in s}x_i^{k_i},$$
--   where $\binom{n}{(k_i)}=n!/\prod_i k_i!$ is the multinomial coefficient.
--
--   It generalises the binomial theorem to any number of summands. It is the basic counting identity behind the multinomial distribution and the expansion of $e^{x_1+\cdots+x_m}$.
--
--   **Formalization note.** The platform's older `Multinomial_Theorem` entry is a deprecated placeholder stating only `True`; this is the actual theorem. `s.piAntidiag n` is the finset of functions `k` supported on `s` with `∑ k = n`, and `Nat.multinomial s k` is the multinomial coefficient. Mathlib: `Finset.sum_pow_eq_sum_piAntidiag`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.sum_pow_eq_sum_piAntidiag`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem multinomial_theorem {α R : Type*} [DecidableEq α] [CommSemiring R] (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n = ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : R) * ∏ i ∈ s, f i ^ k i := by sorry

end FamousTheorems
