-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubicTriangle_endpoint_budget
-- name    : DerivativeChainContinuation.cubicTriangle_endpoint_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:23:08.230568+00:00
-- url     : https://prove2.me/theorems/a59398d1-19e8-4342-a418-07ef24294d49
-- title:
--   Sharp endpoint budget for the cubic triangle
-- statement:
--   Write $\rho_\star=(1+\sqrt{10})/3$. For $0\le k\le1$, $s\ge0$, $s^2\le3$, suppose the explicit points $A(k,s),B(k,s),C(k,s)$ lie in a closed disk of center $o$ and radius $R\ge0$. Then
--
--   $$1+ks/3\le\rho_\star R.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicMetric.lean#L6-L40

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainContinuation_SharpCubicTriangle
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.cubicTriangle_endpoint_budget (k s : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hs0 : 0 ≤ s) (hs3 : s^2 ≤ 3) (o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ‖cubicTriangleA k s-o‖ ≤ R) (hb : ‖cubicTriangleB k s-o‖ ≤ R)
    (hc : ‖cubicTriangleC k s-o‖ ≤ R) :
    1+k*s/3 ≤ sharpCubicConstant*R := by sorry
