-- Prove2me | Theorems.Thm_CarryRNG_AWC_iterate_r_mem_periodicPts
-- name    : CarryRNG.AWC.iterate_r_mem_periodicPts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:02.223999+00:00
-- url     : https://prove2.me/theorems/fa68b6c1-2542-43b2-bbd7-628ce4236b65
-- title:
--   p. 472 — every add-with-carry sequence is periodic after at most $r$ iterations
-- statement:
--   Let $b \ge 2$ be a base, $0 < s < r$ lags, and $f$ the add-with-carry map. For every seed $x$, the state $f^r(x)$ is a periodic point of $f$: there is $p \ge 1$ with
--
--   $$
--   f^{p}\bigl(f^r(x)\bigr) = f^r(x).
--   $$
--
--   Hence the generated sequence $x, f(x), f^2(x), \dots$ is periodic from the $r$-th iterate on, possibly after a short preperiod: "after a few iterations (at most $r$), the periodic cycle begins". Without the bound $r$ the statement would hold for any self-map of a finite set; the content is that the preperiod never exceeds $r$.
--
--   **Formalization Note** Periodicity is Mathlib's `Function.periodicPts`.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5

import Mathlib
import Definitions.Def_CarryRNG_AWC_step

namespace CarryRNG.AWC

theorem iterate_r_mem_periodicPts (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    (step b L)^[L.r] z ∈ Function.periodicPts (step b L) := by sorry

end CarryRNG.AWC
