-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cube_radical_real_remainder_bounds
-- name    : DerivativeChainPrivate.cube_radical_real_remainder_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:08:37.824465+00:00
-- url     : https://prove2.me/theorems/e3457650-96df-42dd-8f23-80716321aad2
-- title:
--   Quantitative real bounds for the cube radical remainder
-- statement:
--   Let real $x,y,p,D,a,b,r$ satisfy $x>0$, $y\ne0$, $U=x^2+y^2\ge5/2$, $p\ge9/10$, $D\ge3$, $2/5\le a\le3/5$, $a^2+b^2\le9/25$, $0\le r\le3/2$, and $6pU^2Db=xy$. Put $P=16a+a^2-b^2$, $Q=b(16+2a)$, $A=r(P+(y/x)Q)/(336U)$, and $B=r((x/y)Q-P)/(336U)$. Then
--
--   $$0\le A\le1/50,\quad-1/50\le B\le0,\quad0\le(3A-B)/2\le1/25.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L476-L567

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.cube_radical_real_remainder_bounds (x y p D a b r : ℝ)
    (hx : 0 < x) (hy : y ≠ 0) (hU : 5 / 2 ≤ x ^ 2 + y ^ 2)
    (hp : 9 / 10 ≤ p) (hD : 3 ≤ D)
    (ha : 2 / 5 ≤ a) (ha' : a ≤ 3 / 5) (hab : a ^ 2 + b ^ 2 ≤ (3 / 5 : ℝ) ^ 2)
    (hr : 0 ≤ r) (hr' : r ≤ 3 / 2)
    (hkey : 6 * p * (x ^ 2 + y ^ 2) ^ 2 * D * b = x * y) :
    let U := x ^ 2 + y ^ 2
    let P := 16 * a + a ^ 2 - b ^ 2
    let Q := b * (16 + 2 * a)
    let A := r / (336 * U) * (P + (y / x) * Q)
    let B := r / (336 * U) * ((x / y) * Q - P)
    0 ≤ A ∧ A ≤ 1 / 50 ∧ -(1 / 50) ≤ B ∧ B ≤ 0 ∧
      0 ≤ (3 * A - B) / 2 ∧ (3 * A - B) / 2 ≤ 1 / 25 := by sorry
