-- Prove2me | Theorems.Thm_BMO5_halt_levels_sparse
-- name    : BMO5.halt_levels_sparse
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T17:26:50.294579+00:00
-- url     : https://prove2.me/theorems/80aa7399-f4ae-486e-aeb2-4b0ef89a286d
-- title:
--   BMO #5: possible halting levels have density zero ($2^{D+1}$ classes mod $2\cdot 3^D$)
-- statement:
--   Let $f(x) = 10\cdot 2^x - 1$, $(a_0,b_0) = (0,5)$, and $(a_{n+1},b_{n+1}) = (a_n+1, b_n - f(a_n))$ if $b_n \ge f(a_n)$, otherwise $(a_n, 3b_n + a_n + 5)$ (Beaver Math Olympiad problem 5; the machine halts iff $b_n = f(a_n) - 1$).
--
--   **Theorem.** For every $D$ there is a set $S$ of at most $2^{D+1}$ residues modulo $2\cdot 3^D$ and a threshold $i_0$ such that any halt at a level $a_n \ge i_0$ has $a_n \bmod 2\cdot 3^D \in S$.
--
--   Since $2^{D+1}/(2\cdot 3^D) = (2/3)^D \to 0$, the levels at which the machine could still halt form a set of natural density zero. This is a necessary condition on where a halt can happen; it does not prove that the machine never halts. It reduces to `BMO5.adm_of_halt`, `BMO5.adm_periodic` and `BMO5.adm_count`.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad. Original result of this submission; builds on BMO5.level_halt_dvd, BMO5.three_adic_uniqueness, BMO5.halt_level_mod18.

import Mathlib

namespace BMO5
theorem halt_levels_sparse (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ D, ∃ S : Finset ℕ, S.card ≤ 2 ^ (D + 1) ∧ ∃ i0, ∀ n, b n = 10 * 2 ^ (a n) - 2 → i0 ≤ a n →
      a n % (2 * 3 ^ D) ∈ S := by
  sorry
end BMO5
