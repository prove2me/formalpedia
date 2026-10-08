-- Prove2me | Theorems.Thm_CarryRNG_SWB_periodic_seed_iff
-- name    : CarryRNG.SWB.periodic_seed_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:40.740985+00:00
-- url     : https://prove2.me/theorems/8a07a394-ad70-40dc-9580-158a0d9c39eb
-- title:
--   p. 472, Method 1 — classification of periodic seeds
-- statement:
--   Let $b\ge2$, $0<s<r$, and write $A=x_r\cdots x_{s+1}$ and $B=x_{r-s}\cdots x_1$ as base-$b$ integers. A Method 1 seed $(x_1,\ldots,x_r,c)$ is strictly periodic exactly in these cases:
--   $$
--   (c=0\ \text{and}\ A<B)\quad\text{or}\quad
--   (c=1\ \text{and}\ B<A)\quad\text{or}\quad
--   (0,\ldots,0,0)\quad\text{or}\quad(b-1,\ldots,b-1,1).
--   $$
--   The two named seeds are fixed points; the strict inequalities classify every nontrivial periodic seed. This is the paper’s Method 1 rule, with digit strings interpreted as integers.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5, Method 1

import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_SWB_highBlock
import Definitions.Def_CarryRNG_SWB_lowBlock
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.SWB

/-- Page 472, Method 1: the strict inequalities classify the nontrivial periodic seeds. -/
theorem periodic_seed_iff (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    z ∈ Function.periodicPts (step b L hb) ↔
      (z.c.val = 0 ∧ highBlock b L z < lowBlock b L z) ∨
      (z.c.val = 1 ∧ lowBlock b L z < highBlock b L z) ∨
      z = CarryRNG.AWC.zeroSeed b L.r hb ∨ z = CarryRNG.AWC.topSeed b L.r hb := by sorry

end CarryRNG.SWB
