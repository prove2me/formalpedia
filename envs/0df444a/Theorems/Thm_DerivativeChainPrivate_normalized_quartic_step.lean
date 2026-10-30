-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_quartic_step
-- name    : DerivativeChainPrivate.normalized_quartic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:34:30.65934+00:00
-- url     : https://prove2.me/theorems/fdf0b994-2d8c-497e-97a6-3f948aa5c93e
-- title:
--   A northeast quartic selection with a variable constant
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Let $0\le c\le8/21$ and $w^3-w=\beta$ with $\operatorname{Re}w>0$. There is $z$ with $z^4-2z^2-4\beta z+c=0$, both coordinates at least those of $w$, $(\operatorname{Re}z)^2\ge7/4$, and $\beta/z=z^2/4-1/2+(c/4)/z^2$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/QuarticStep.lean#L8-L100

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_quartic_step (c : ℝ) (hc : 0 ≤ c) (hcUpper : c ≤ 8/21) (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hw : w ^ 3 - w = β) (hwpos : 0 < w.re) :
    ∃ z : ℂ,
      z ^ 4 - 2 * z ^ 2 - 4 * β * z + c = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7 / 4 ≤ z.re ^ 2 ∧
      β / z = (1/4 : ℂ) * z ^ 2 - 1/2 + (c/4 : ℂ) / z ^ 2 := by sorry
