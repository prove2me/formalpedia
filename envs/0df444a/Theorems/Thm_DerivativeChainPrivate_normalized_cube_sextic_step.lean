-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cube_sextic_step
-- name    : DerivativeChainPrivate.normalized_cube_sextic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:14:24.673562+00:00
-- url     : https://prove2.me/theorems/e619dd56-445e-4607-b836-48341171364a
-- title:
--   A northeast sextic parent of the cube quintic row
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $Q_3(z)=z^3-z-\beta$, $Q_4(z)=z^4-2z^2-4\beta z+8/21$, $Q_5(z)=z^5-(10/3)z^3-10\beta z^2+(40/21)z+(16/3)\beta$, and $Q_6(z)=z^6-5z^4-20\beta z^3+(40/7)z^2+32\beta z-16/21+28\beta^2$. Let $x=\operatorname{Re}w>0$, $x^2\ge5/2$, $Q_5(w)=0$, and $\beta/w=w^2/10-7/25+(36/875)/(w^2-8/15)$. There is a root $z$ of $Q_6$ with both coordinates at least those of $w$, $(\operatorname{Re}z)^2\ge5/2$, and $\operatorname{Im}z\ge0$. It admits real $\alpha>1/28$, $b-1/7>1/25$ and complex $e$ with $\beta/z=\alpha z^2-b+e/z$, with $\operatorname{Im}\beta=0\Rightarrow\operatorname{Im}z=0$ and $(3\operatorname{Re}e/\operatorname{Re}z-\operatorname{Im}e/\operatorname{Im}z)/2\le1/25$ whenever $\operatorname{Im}z\ne0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1402-L1456

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cube_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-10/3*w^3-10*β*w^2+40/21*w+16/3*β = 0)
    (hwinv : β/w = (1/10 : ℂ)*w^2-7/25+(36/875 : ℂ)/(w^2-8/15)) :
    ∃ z : ℂ, z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re^2 ∧ 0 ≤ z.im ∧
      ∃ (α b : ℝ) (e : ℂ), 1/28 < α ∧ 1/25 < b-1/7 ∧
        β/z = (α : ℂ)*z^2-(b : ℂ)+e/z ∧ (β.im = 0 → z.im = 0) ∧
        (z.im ≠ 0 → (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/25) := by sorry
