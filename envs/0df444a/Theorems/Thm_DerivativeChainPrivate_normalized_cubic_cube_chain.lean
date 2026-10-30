-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cubic_cube_chain
-- name    : DerivativeChainPrivate.normalized_cubic_cube_chain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:18:53.099767+00:00
-- url     : https://prove2.me/theorems/8eb6d099-a4eb-422f-8158-1b07c22cdba1
-- title:
--   A complete monotone nine-row chain for the normalized cube
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $p(X)=(X^3-4X-28\beta)^3$. There is $z\in\mathbb C^9$ with $p^{(8-i)}(z_i)=0$, $z_0=0$, $z_6=z_7=z_8$, $z_8^3-4z_8-28\beta=0$, and $\operatorname{Re}z_8>0$. Both coordinates are nondecreasing and $L(z)\le\sqrt2\,|z_8|$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1528-L1600

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cubic_cube_chain (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 9 → ℂ,
      (∀ i, (derivative^[9-(i.val+1)] ((X^3-4*X-28*C β)^3)).eval (z i) = 0) ∧
      z 0 = 0 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧
      (z 8)^3-4*z 8-28*β = 0 ∧ 0 < (z 8).re ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2 * ‖z 8‖ := by sorry
