-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cube_quartic_step
-- name    : DerivativeChainPrivate.normalized_cube_quartic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:03:05.241206+00:00
-- url     : https://prove2.me/theorems/974887e8-81b8-4b97-940f-e7ac48dbd1fc
-- title:
--   A northeast quartic parent of the normalized cubic root
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $Q_3(z)=z^3-z-\beta$, $Q_4(z)=z^4-2z^2-4\beta z+8/21$, $Q_5(z)=z^5-(10/3)z^3-10\beta z^2+(40/21)z+(16/3)\beta$, and $Q_6(z)=z^6-5z^4-20\beta z^3+(40/7)z^2+32\beta z-16/21+28\beta^2$. If $Q_3(w)=0$ and $\operatorname{Re}w>0$, there is $z$ with $Q_4(z)=0$, both coordinates at least those of $w$, $(\operatorname{Re}z)^2\ge7/4$, and
--
--   $$\beta/z=z^2/4-1/2+(2/21)/z^2.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L801-L893

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cube_quartic_step (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hw : w ^ 3 - w = β) (hwpos : 0 < w.re) :
    ∃ z : ℂ,
      z ^ 4 - 2 * z ^ 2 - 4 * β * z + 8 / 21 = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7 / 4 ≤ z.re ^ 2 ∧
      β / z = (1/4 : ℂ) * z ^ 2 - 1/2 + (2/21 : ℂ) / z ^ 2 := by sorry
