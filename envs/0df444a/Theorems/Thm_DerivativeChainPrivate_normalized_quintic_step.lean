-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_quintic_step
-- name    : DerivativeChainPrivate.normalized_quintic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:37:17.057812+00:00
-- url     : https://prove2.me/theorems/fca601d4-79e4-45c7-91ec-1a4f133111cd
-- title:
--   A northeast quintic selection for compatible coefficient data
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Let real $c,d,b,e$ satisfy $0\le c\le8/21$, $0\le d\le8/15$, $b\le3/10$, $0\le e<1/10$, $10b+d=10/3$, and $10(e+bd)=5c$. Suppose $\operatorname{Re}w>0$, $\operatorname{Im}w\ge0$, $(\operatorname{Re}w)^2\ge7/4$, $w^4-2w^2-4\beta w+c=0$, and $\beta/w=w^2/4-1/2+(c/4)/w^2$. There is a northeast point $z$ with $(\operatorname{Re}z)^2\ge5/2$,
--
--   $$z^5-\tfrac{10}3z^3-10\beta z^2+5cz+10d\beta=0,\qquad\beta/z=z^2/10-b+e/(z^2-d).$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/QuinticStep.lean#L8-L151

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_quintic_step (c d b e : ℝ)
    (hc : 0 ≤ c) (hcUpper : c ≤ 8/21) (hd : 0 ≤ d) (hdUpper : d ≤ 8/15)
    (hbUpper : b ≤ 3/10) (he : 0 ≤ e) (heUpper : e < 1/10)
    (hsum : 10*b+d = 10/3) (hcoeff : 10*(e+b*d) = 5*c) (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwX : 7/4 ≤ w.re ^ 2)
    (hwroot : w ^ 4 - 2 * w ^ 2 - 4 * β * w + c = 0)
    (hwinv : β / w = (1/4 : ℂ) * w ^ 2 - 1/2 + ((c/4) : ℂ) / w ^ 2) :
    ∃ z : ℂ,
      z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + (5*c) * z + (10*d) * β = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re ^ 2 ∧
      β / z = (1/10 : ℂ) * z ^ 2 - b + (e : ℂ) / (z ^ 2 - d) := by sorry
