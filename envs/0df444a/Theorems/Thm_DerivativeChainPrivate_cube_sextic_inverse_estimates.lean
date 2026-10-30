-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cube_sextic_inverse_estimates
-- name    : DerivativeChainPrivate.cube_sextic_inverse_estimates
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:11:03.261752+00:00
-- url     : https://prove2.me/theorems/417bff2c-2bad-45ab-81b5-114d8d84ad53
-- title:
--   Quantitative inverse branches for the cube sextic row
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $Q_3(z)=z^3-z-\beta$, $Q_4(z)=z^4-2z^2-4\beta z+8/21$, $Q_5(z)=z^5-(10/3)z^3-10\beta z^2+(40/21)z+(16/3)\beta$, and $Q_6(z)=z^6-5z^4-20\beta z^3+(40/7)z^2+32\beta z-16/21+28\beta^2$. Let $Q_6(z)=0$, $x=\operatorname{Re}z>0$, $x^2\ge5/2$, and put $y=\operatorname{Im}z$. There are real $\alpha,b$ and complex $e$ with $\alpha>1/28$, $b-1/7>1/25$, and $\beta/z=\alpha z^2-b+e/z$. Moreover $y\ge0$ and $y=0$ exactly when $\operatorname{Im}\beta=0$. For $y\ne0$, set $C=(3\operatorname{Re}e/x-\operatorname{Im}e/y)/2$; then $C\le1/25$. One of two alternatives holds: $\alpha<1/10$, $7/25-b>1/12$, and $C\ge0$ when defined; or $\alpha>3/5$, $b<1$, and $\operatorname{Re}e/x\ge-1/50$ when $y\ne0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1307-L1391

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.cube_sextic_inverse_estimates (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hroot : z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0) :
    ∃ (α b : ℝ) (e : ℂ),
      1/28 < α ∧ 1/25 < b-1/7 ∧ β/z = (α : ℂ)*z^2-(b : ℂ)+e/z ∧
      0 ≤ z.im ∧ (β.im = 0 → z.im = 0) ∧ (z.im = 0 → β.im = 0) ∧
      (z.im ≠ 0 → (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/25) ∧
      ((α < 1/10 ∧ 1/12 < 7/25-b ∧ (z.im ≠ 0 → 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2)) ∨
        (3/5 < α ∧ b < 1 ∧ (z.im ≠ 0 → -(1/50) ≤ e.re/z.re))) := by sorry
