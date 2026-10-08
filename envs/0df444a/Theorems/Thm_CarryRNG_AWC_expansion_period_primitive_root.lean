-- Prove2me | Theorems.Thm_CarryRNG_AWC_expansion_period_primitive_root
-- name    : CarryRNG.AWC.expansion_period_primitive_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:20.432378+00:00
-- url     : https://prove2.me/theorems/bc89acc5-7723-4cd9-a447-fd7848c6b26f
-- title:
--   §4.1 — if $b$ is a primitive root of the prime $m$, every proper fraction $k/m$ has period $m - 1$
-- statement:
--   Let $b \ge 2$ be a base and $m$ a prime for which $b$ is a primitive root, i.e. the multiplicative order of $b$ modulo $m$ is $m - 1$. Let $0 < k < m$, and write $d_1, d_2, \dots$ for the base-$b$ digits of $k/m$ after the point. Then for every $p > 0$,
--
--   $$
--   \bigl(d_{j+p} = d_j \text{ for all } j \ge 1\bigr) \iff (m - 1) \mid p ,
--   $$
--
--   so the base-$b$ expansion of every proper fraction $k/m$ is strictly periodic with least period $m - 1$. This is why the paper seeks primes $m = b^r \pm b^s \pm 1$ having $b$ as a primitive root: the generators built on them attain the longest possible period.
--
--   **Formalization Note** "Primitive root" is the hypothesis `orderOf (b : ZMod m) = m - 1`.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.1 ("For our purposes, we want to choose primes m for which b is a primitive root. Then the period is m - 1 ...")

import Mathlib
import Definitions.Def_CarryRNG_AWC_digit

namespace CarryRNG.AWC

theorem expansion_period_primitive_root (b m k : ℕ) (hb : 2 ≤ b) (hm : m.Prime)
    (hroot : orderOf (b : ZMod m) = m - 1) (hk0 : 0 < k) (hk : k < m) (p : ℕ) (hp : 0 < p) :
    (∀ j, 1 ≤ j → digit b m k (j + p) = digit b m k j) ↔ (m - 1) ∣ p := by sorry

end CarryRNG.AWC
