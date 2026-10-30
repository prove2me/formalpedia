-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubicFourthSharpChainRadius
-- name    : DerivativeChainContinuation.cubicFourthSharpChainRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:30:15.741957+00:00
-- url     : https://prove2.me/theorems/9dd6224b-39c6-4bdb-8154-0329a5a0328e
-- title:
--   Sharp chain-length bound for a monic cubic power 4
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Write $\rho_\star=(1+\sqrt{10})/3$. Let $q\in\mathbb C[X]$ be monic of degree three, and suppose every root lies in the closed disk of center $o$ and radius $R\ge0$. There is $z\in\mathbb C^{12}$ satisfying $[q^{4}]^{(12-i-1)}(z_i)=0$, starting at the mean of the three roots counted with multiplicity, constant from index 8 onward, and ending at a root of $q$. It admits unit orthogonal complex frame coefficients with nondecreasing projected coordinates and satisfies $L(z)\le\rho_\star R$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicPowers.lean#L8-L23

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.cubicFourthSharpChainRadius (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x - o‖ ≤ R) :
    ∃ (z : Fin 12 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[12 - (i.val + 1)] (q^4)).eval (z i) = 0) ∧
      z 0 = q.roots.sum / 3 ∧
      (∀ i : Fin 12, 8 ≤ i.val → z i = z 11) ∧ q.eval (z 11) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a * starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a * z i).re) ∧ Monotone (fun i => (b * z i).re) ∧
      chainCost z ≤ sharpCubicConstant * R := by sorry
