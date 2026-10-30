-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cube_source_step
-- name    : DerivativeChainPrivate.normalized_cube_source_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:16:53.808547+00:00
-- url     : https://prove2.me/theorems/041c5cab-cfde-48a4-b501-89b5c4ad5e9d
-- title:
--   A northeast source-cubic endpoint from the sextic row
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $Q_3(z)=z^3-z-\beta$, $Q_4(z)=z^4-2z^2-4\beta z+8/21$, $Q_5(z)=z^5-(10/3)z^3-10\beta z^2+(40/21)z+(16/3)\beta$, and $Q_6(z)=z^6-5z^4-20\beta z^3+(40/7)z^2+32\beta z-16/21+28\beta^2$. Let $Q_6(w)=0$, $\operatorname{Re}w>0$, $\operatorname{Im}w\ge0$. Assume real $\alpha>1/28$, $b-1/7>1/25$ and complex $e$ satisfy $\beta/w=\alpha w^2-b+e/w$, $\operatorname{Im}\beta=0\Rightarrow\operatorname{Im}w=0$, and $(3\operatorname{Re}e/\operatorname{Re}w-\operatorname{Im}e/\operatorname{Im}w)/2\le1/25$ when $\operatorname{Im}w\ne0$. There exists $z$ with $z^3-4z-28\beta=0$, both coordinates at least those of $w$, and $\operatorname{Re}z>0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1467-L1517

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cube_source_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwroot : w^6-5*w^4-20*β*w^3+40/7*w^2+32*β*w-16/21+28*β^2 = 0)
    (α b : ℝ) (e : ℂ) (hα : 1/28 < α) (hb : 1/25 < b-1/7)
    (hgraph : β/w = (α : ℂ)*w^2-(b : ℂ)+e/w)
    (hwzero : β.im = 0 → w.im = 0)
    (hC : w.im ≠ 0 → (3*(e.re/w.re)-e.im/w.im)/2 ≤ 1/25) :
    ∃ z : ℂ, z^3-4*z-28*β = 0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.re := by sorry
