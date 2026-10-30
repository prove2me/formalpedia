-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fourth_prefix_five
-- name    : DerivativeChainPrivate.normalized_fourth_prefix_five
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:25:05.091911+00:00
-- url     : https://prove2.me/theorems/7d47c0f0-06f2-49a0-894a-9d1ef518be2d
-- title:
--   An actual five-vertex prefix for cubic power 4
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $p(X)=(X^3-11/2X-55\beta)^{4}$. There is $z\in\mathbb C^5$ with $p^{(12-i-1)}(z_i)=0$ for $0\le i<5$, $z_0=0$, and both coordinates nondecreasing. Its last point has positive real part, $(\operatorname{Re}z_4)^2\ge5/2$, and
--
--   $$\beta/z_4=z_4^2/10-23/80+\frac{33/640}{z_4^2-11/24}.$$
--
--   This supplies only the first five vertices of the 12-vertex derivative tower.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/PrefixFive.lean#L10-L72

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fourth_prefix_five (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[12-(i.val+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(23/80)+(33/640)/((z 4)^2-(11/24)) := by sorry
