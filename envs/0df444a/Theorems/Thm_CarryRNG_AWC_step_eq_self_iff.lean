-- Prove2me | Theorems.Thm_CarryRNG_AWC_step_eq_self_iff
-- name    : CarryRNG.AWC.step_eq_self_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:20.710156+00:00
-- url     : https://prove2.me/theorems/65299bc1-b36c-4a3c-8918-e413b323694a
-- title:
--   p. 472 — the two trivial seeds are the only fixed points of the add-with-carry map
-- statement:
--   Let $b \ge 2$ be a base, $0 < s < r$ lags, and $f$ the add-with-carry map. For every state $x = (x_1, \dots, x_r, c)$,
--
--   $$
--   f(x) = x \iff x = (0, \dots, 0, 0) \ \text{ or } \ x = (b-1, \dots, b-1, 1).
--   $$
--
--   So the two trivial seeds of Section 4.5 generate the only sequences of period $1$ ("two short periods, each of length 1"), and every other seed is excluded from the period statement only because of this.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5 ("There are two short periods, each of length 1, for the trivial seed vectors (0, ..., 0, 0) and (b - 1, ..., b - 1, 1).")

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.AWC

theorem step_eq_self_iff (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    step b L z = z ↔ z = zeroSeed b L.r hb ∨ z = topSeed b L.r hb := by sorry

end CarryRNG.AWC
