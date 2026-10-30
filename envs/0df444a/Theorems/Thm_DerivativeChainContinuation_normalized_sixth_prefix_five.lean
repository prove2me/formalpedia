-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_sixth_prefix_five
-- name    : DerivativeChainContinuation.normalized_sixth_prefix_five
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:40:20.99714+00:00
-- url     : https://prove2.me/theorems/d0f5545d-65f7-4c4e-a6ec-a71aa63b5324
-- title:
--   An actual five-vertex prefix for cubic power 6
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $p(X)=(X^3-17/2X-136\beta)^{6}$. There is $z\in\mathbb C^5$ with $p^{(18-i-1)}(z_i)=0$ for $0\le i<5$, $z_0=0$, and both coordinates nondecreasing. Its last point has positive real part, $(\operatorname{Re}z_4)^2\ge5/2$, and
--
--   $$\beta/z_4=z_4^2/10-41/140+\frac{459/7840}{z_4^2-17/42}.$$
--
--   This supplies only the first five vertices of the 18-vertex derivative tower.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Power678PrefixFive.lean#L12-L74

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.normalized_sixth_prefix_five (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(41/140)+(459/7840)/((z 4)^2-(17/42)) := by sorry
