-- Prove2me | Theorems.Thm_CarryRNG_AWC_example_base10_period
-- name    : CarryRNG.AWC.example_base10_period
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:15.152975+00:00
-- url     : https://prove2.me/theorems/1e2a1663-e343-4d08-8554-98cd09b36414
-- title:
--   §2, p. 465 — the generator $x_n = x_{n-2} + x_{n-1} + c \bmod 10$ has period 108
-- statement:
--   Take base $b = 10$ and lags $r = 2$, $s = 1$, so that the add-with-carry map is
--
--   $$
--   f(x_1, x_2, c) = \begin{cases} (x_2,\ x_1 + x_2 + c,\ 0) & \text{if } x_1 + x_2 + c < 10,\\ (x_2,\ x_1 + x_2 + c - 10,\ 1) & \text{if } x_1 + x_2 + c \ge 10. \end{cases}
--   $$
--
--   1. If the seed is $x = (x_1, x_2, 0)$ with $x_1 < x_2$, or $x = (x_1, x_2, 1)$ with $x_1 > x_2$, then the sequence $x, f(x), f^2(x), \dots$ is strictly periodic with least period $108$.
--   2. If the seed $x$ is of neither type and is not one of the trivial seeds $(0, 0, 0)$ and $(9, 9, 1)$, then the sequence beginning with $f(x)$ is strictly periodic with least period $108$.
--
--   Here $m = 10^2 + 10 - 1 = 109$ is prime and $108$ is the order of $10$ modulo $109$; the statement is a concrete instance of the general period theorem of the mission.
--
--   **Formalization Note** The paper prints the second trivial seed as "$(9, 9, 9)$"; the third entry is the carry bit, so the seed meant is $(9, 9, 1)$, the trivial seed $(b-1, b-1, 1)$ of p. 472. "Period 108" is stated as `Function.minimalPeriod f _ = 108`.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 465, Section 2

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.AWC

theorem example_base10_period :
    let L : Lags := ⟨2, 1, by norm_num, by norm_num⟩
    (∀ z : State 10 L.r,
        (z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0) →
        Function.minimalPeriod (step 10 L) z = 108) ∧
    (∀ z : State 10 L.r,
        ¬ ((z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0)) →
        z ≠ zeroSeed 10 L.r (by norm_num) → z ≠ topSeed 10 L.r (by norm_num) →
        Function.minimalPeriod (step 10 L) (step 10 L z) = 108) := by sorry

end CarryRNG.AWC
