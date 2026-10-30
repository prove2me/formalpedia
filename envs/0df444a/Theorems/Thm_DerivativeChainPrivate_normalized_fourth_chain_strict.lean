-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fourth_chain_strict
-- name    : DerivativeChainPrivate.normalized_fourth_chain_strict
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:27:44.899116+00:00
-- url     : https://prove2.me/theorems/ee916fd9-c95c-4129-b8ce-4e62a511ed37
-- title:
--   A complete twelve-row chain for strict normalized fourth powers
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Let $\operatorname{Re}\beta\ge0$, $\operatorname{Im}\beta>0$, and $p(X)=(X^3-(11/2)X-55\beta)^4$. There is $z\in\mathbb C^{12}$ with $p^{(11-i)}(z_i)=0$, $z_0=0$, a constant suffix from index eight, and $z_{11}^3-(11/2)z_{11}-55\beta=0$. Both coordinates are nondecreasing and $L(z)\le\sqrt2\,|z_{11}|$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/FourthNormalizedChain.lean#L11-L106

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fourth_chain_strict (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im) :
    ∃ z : Fin 12 → ℂ,
      (∀ i, (derivative^[12-(i.val+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin 12, 8 ≤ i.val → z i=z 11) ∧
      (z 11)^3-(11/2)*z 11-55*β=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z 11‖ := by sorry
