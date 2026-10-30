-- Prove2me | Theorems.Thm_DerivativeChainContinuation_three_point_radius_lower_bound
-- name    : DerivativeChainContinuation.three_point_radius_lower_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:15:11.401995+00:00
-- url     : https://prove2.me/theorems/22e2d6e1-b9f7-4645-a24c-c9633222310e
-- title:
--   Containing-disk bound for a nonobtuse triangle
-- statement:
--   Let $a,b,c,o\in\mathbb C$ and $R\ge0$ with $|a-o|,|b-o|,|c-o|\le R$. Put $U=|a-b|^2$, $V=|a-c|^2$, $W=|b-c|^2$. Assume $U\le V+W$, $V\le U+W$, $W\le U+V$, and $\Delta=2(UV+UW+VW)-U^2-V^2-W^2>0$. Then
--
--   $$UVW\le\Delta R^2.$$
--
--   This gives the circumradius obstruction to a smaller containing disk.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ThreePointRadius.lean#L14-L50

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.three_point_radius_lower_bound (a b c o : ℂ) (R U V W : ℝ)
    (hR : 0 ≤ R) (ha : ‖a-o‖ ≤ R) (hb : ‖b-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hU : Complex.normSq (a-b)=U) (hV : Complex.normSq (a-c)=V)
    (hW : Complex.normSq (b-c)=W)
    (hu : 0 ≤ V+W-U) (hv : 0 ≤ U+W-V) (hw : 0 ≤ U+V-W)
    (hs : 0 < 2*(U*V+U*W+V*W)-U^2-V^2-W^2) :
    U*V*W ≤ (2*(U*V+U*W+V*W)-U^2-V^2-W^2)*R^2 := by sorry
