-- Prove2me | Theorems.Thm_CarryRNG_AWC_die_generator_period
-- name    : CarryRNG.AWC.die_generator_period
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:29.460861+00:00
-- url     : https://prove2.me/theorems/3762718c-e308-4456-ac8d-cbd22967ef3f
-- title:
--   §7, p. 477 — the die generator $x_n = x_{n-21} + x_{n-2} + c \bmod 6$ has period $6^{21} + 6^2 - 2$
-- statement:
--   Consider the add-with-carry generator with base $b = 6$ and lags $r = 21$, $s = 2$, that is $x_n = x_{n-21} + x_{n-2} + c \bmod 6$, and let $m = 6^{21} + 6^2 - 1$. Then:
--
--   1. $m$ is prime;
--   2. $6$ is a primitive root of $m$: its multiplicative order modulo $m$ is $m - 1 = 6^{21} + 6^2 - 2$;
--   3. for every seed of $21$ digits and an initial carry $c$, other than $21$ zeros with $c = 0$ and $21$ fives with $c = 1$, the generated sequence is periodic from the $21$st iterate on, with least period
--
--   $$6^{21} + 6^2 - 2 = 21{,}936{,}950{,}640{,}377{,}890 .$$
--
--   The paper offers this generator for classroom use, as a simulation of throws of a die.
--
--   **Formalization Note** The paper says the period holds "for any set of 21 seed digits"; by the paper's own remark on p. 472 (the cycle begins after at most $r$ iterations) the period is attained from $f^{21}(x)$ on, which is how part 3 is stated.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 477, Section 7

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.AWC

theorem die_generator_period :
    let L : Lags := ⟨21, 2, by norm_num, by norm_num⟩
    (6 ^ 21 + 6 ^ 2 - 1).Prime ∧
    orderOf (6 : ZMod (6 ^ 21 + 6 ^ 2 - 1)) = 6 ^ 21 + 6 ^ 2 - 2 ∧
    ∀ z : State 6 L.r, z ≠ zeroSeed 6 L.r (by norm_num) → z ≠ topSeed 6 L.r (by norm_num) →
      Function.minimalPeriod (step 6 L) ((step 6 L)^[21] z) = 21936950640377890 := by sorry

end CarryRNG.AWC
