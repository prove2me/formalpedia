-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_triple_normalization_parameters
-- name    : DerivativeChainPrivate.cubic_triple_normalization_parameters
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:59:40.274532+00:00
-- url     : https://prove2.me/theorems/201136ac-c494-42b5-870e-da8e19f14d1c
-- title:
--   Affine normalization of a cubic with nonzero quadratic moment
-- statement:
--   For a triple $u,v,w$ put $m=(u+v+w)/3$ and $D=(u^2+v^2+w^2-uv-uw-vw)/3$. For arbitrary complex $u,v,w$ with $D\ne0$ and prescribed real $a,b>0$, there exist $c\ne0$ and $\beta\in\mathbb C$ with $\operatorname{Re}\beta\ge0$ such that, for $q(X)=(X-u)(X-v)(X-w)$,
--
--   $$q(m+cX)=c^3(X^3-aX-b\beta).$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/PowerNormalization.lean#L8-L43

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.cubic_triple_normalization_parameters (u v w : ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    ∃ c β : ℂ, c ≠ 0 ∧ 0 ≤ β.re ∧
      ((X-C u)*(X-C v)*(X-C w)).comp (C ((u+v+w)/3)+C c*X) =
        C (c^3)*(X^3-C (a:ℂ)*X-C ((b:ℂ)*β)) := by sorry
