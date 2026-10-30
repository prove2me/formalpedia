-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_seventh_prefix_five
-- name    : DerivativeChainContinuation.normalized_seventh_prefix_five
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:48:59.341203+00:00
-- url     : https://prove2.me/theorems/99dd4e69-cce1-4dcc-acb6-c06a642c1d44
-- title:
--   An actual five-vertex prefix for cubic power 7
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $p(X)=(X^3-10X-190\beta)^{7}$. There is $z\in\mathbb C^5$ with $p^{(21-i-1)}(z_i)=0$ for $0\le i<5$, $z_0=0$, and both coordinates nondecreasing. Its last point has positive real part, $(\operatorname{Re}z_4)^2\ge5/2$, and
--
--   $$\beta/z_4=z_4^2/10-5/17+\frac{330/5491}{z_4^2-20/51}.$$
--
--   This supplies only the first five vertices of the 21-vertex derivative tower.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Power678PrefixFive.lean#L76-L138

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.normalized_seventh_prefix_five (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[21-(i.val+1)] ((X^3-C (10)*X-190*C β)^7)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(5/17)+(330/5491)/((z 4)^2-(20/51)) := by sorry
