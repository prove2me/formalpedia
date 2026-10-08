-- Prove2me | Theorems.Thm_CarryRNG_SWB_expansion_period_eq_orderOf
-- name    : CarryRNG.SWB.expansion_period_eq_orderOf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:19.372017+00:00
-- url     : https://prove2.me/theorems/3360e1ad-3a93-4629-b732-b7f6fae29f06
-- title:
--   §4.1 — period of the base-b digits of k/m
-- statement:
--   Let $b\ge2$ and $m>1$ be integers relatively prime to one another. Let $1\le k<m$ be relatively prime to $m$, and let $d_j$ be the $j$th base-$b$ digit of $k/m$. For every positive integer $p$,
--   $$
--   \bigl(\forall j\ge1,\ d_{j+p}=d_j\bigr)
--   \quad\Longleftrightarrow\quad
--   \operatorname{ord}_m(b)\mid p.
--   $$
--   Consequently the least positive digit period is the multiplicative order of $b$ modulo $m$. This supplies the number-theoretic period used for the generator.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.1

import Definitions.Def_CarryRNG_AWC_digit

namespace CarryRNG.SWB

/-- Section 4.1: the least positive period of the digits of `k/m` is the order of `b` mod `m`. -/
theorem expansion_period_eq_orderOf (b m k p : ℕ) (hb : 2 ≤ b) (hm : 1 < m)
    (hk : 0 < k ∧ k < m) (hkm : Nat.Coprime k m) (hbm : Nat.Coprime b m)
    (hp : 0 < p) :
    (∀ j : ℕ, 1 ≤ j → CarryRNG.AWC.digit b m k (j + p) = CarryRNG.AWC.digit b m k j) ↔
      orderOf (b : ZMod m) ∣ p := by sorry

end CarryRNG.SWB
