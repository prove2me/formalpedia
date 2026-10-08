-- Prove2me | Theorems.Thm_CarryRNG_SWB_primitive_root_expansion_period
-- name    : CarryRNG.SWB.primitive_root_expansion_period
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:11.906653+00:00
-- url     : https://prove2.me/theorems/be4c12f6-6837-45f7-89b5-9735bc790a1f
-- title:
--   §4.1 — a primitive root gives period m − 1
-- statement:
--   Let $m$ be prime, $b\ge2$ be relatively prime to $m$, and $1\le k<m$. Suppose the order of $b$ modulo $m$ is $m-1$, so $b$ is a primitive root. Then, for every positive integer $p$, the base-$b$ digits $d_j$ of $k/m$ satisfy
--   $$
--   \bigl(\forall j\ge1,\ d_{j+p}=d_j\bigr)
--   \quad\Longleftrightarrow\quad (m-1)\mid p.
--   $$
--   Thus every proper fraction with this denominator has least digit period $m-1$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.1

import Definitions.Def_CarryRNG_AWC_digit

namespace CarryRNG.SWB

/-- Section 4.1: a primitive root gives full period `m - 1` for each proper fraction. -/
theorem primitive_root_expansion_period (b m k p : ℕ) (hb : 2 ≤ b) (hm : m.Prime)
    (hk : 0 < k ∧ k < m) (hbm : Nat.Coprime b m)
    (hprim : orderOf (b : ZMod m) = m - 1) (hp : 0 < p) :
    (∀ j : ℕ, 1 ≤ j → CarryRNG.AWC.digit b m k (j + p) = CarryRNG.AWC.digit b m k j) ↔
      m - 1 ∣ p := by sorry

end CarryRNG.SWB
