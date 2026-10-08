-- Prove2me | Theorems.Thm_CarryRNG_AWC_period_eq_orderOf
-- name    : CarryRNG.AWC.period_eq_orderOf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:29.933191+00:00
-- url     : https://prove2.me/theorems/959c13bf-d326-4337-8a05-fdc3aec27504
-- title:
--   §4.2/§4.5 — for prime $m = b^r + b^s - 1$, every nontrivial add-with-carry sequence has period the order of $b$ mod $m$
-- statement:
--   Let $b \ge 2$ be a base and $0 < s < r$ lags such that
--
--   $$m = b^r + b^s - 1$$
--
--   is prime, and let $f$ be the add-with-carry map ($x_n = x_{n-r} + x_{n-s} + c \bmod b$). Let $x$ be any seed other than the two trivial seeds $(0, \dots, 0, 0)$ and $(b-1, \dots, b-1, 1)$. Then the state $f^r(x)$ lies on a cycle of $f$ whose length is the multiplicative order of $b$ modulo $m$:
--
--   $$
--   \min\{p \ge 1 : f^{p}(f^r(x)) = f^r(x)\} = \operatorname{ord}_m(b).
--   $$
--
--   That is, whatever the seed, except for the two trivial seeds, the add-with-carry sequence becomes periodic after at most $r$ iterations of the generating function, and its period is the order of the base $b$ for the modulus $m$. When $b$ is moreover a primitive root of $m$, the period is $m - 1 = b^r + b^s - 2$, the value announced in Section 2.
--
--   **Formalization Note** The left side is Mathlib's `Function.minimalPeriod`, which is $0$ for a point that is not periodic; since $\operatorname{ord}_m(b) \ge 1$, the equation also asserts that $f^r(x)$ is periodic. The period is measured at $f^r(x)$ rather than at $x$ because a seed need not lie on its own cycle (p. 472). The paper's "appropriately chosen" parameters and "a few iterations" are read as "$m$ prime" and "at most $r$", the readings the paper itself gives on pp. 468 and 472.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.2 (claim), p. 468 (proof), p. 472, Section 4.5 (summary)

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed
import Definitions.Def_CarryRNG_AWC_modulus

namespace CarryRNG.AWC

theorem period_eq_orderOf (b : ℕ) (L : Lags) (hb : 2 ≤ b) (hm : (modulus b L).Prime)
    (z : State b L.r) (h0 : z ≠ zeroSeed b L.r hb) (h1 : z ≠ topSeed b L.r hb) :
    Function.minimalPeriod (step b L) ((step b L)^[L.r] z) =
      orderOf (b : ZMod (modulus b L)) := by sorry

end CarryRNG.AWC
