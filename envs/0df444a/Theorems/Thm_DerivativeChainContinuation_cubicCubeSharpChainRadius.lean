-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubicCubeSharpChainRadius
-- name    : DerivativeChainContinuation.cubicCubeSharpChainRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:20:57.743333+00:00
-- url     : https://prove2.me/theorems/94ccb0c9-64b6-4b3f-b35b-7d16140207c1
-- title:
--   Sharp chain-length bound for a monic cubic power 3
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Write $\rho_\star=(1+\sqrt{10})/3$. Let $q\in\mathbb C[X]$ be monic of degree three, and suppose every root lies in the closed disk of center $o$ and radius $R\ge0$. There is $z\in\mathbb C^{9}$ satisfying $[q^{3}]^{(9-i-1)}(z_i)=0$, starting at the mean of the three roots counted with multiplicity, constant from index 6 onward, and ending at a root of $q$. It admits unit orthogonal complex frame coefficients with nondecreasing projected coordinates and satisfies $L(z)\le\rho_\star R$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicPowers.lean#L45-L68

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.cubicCubeSharpChainRadius (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] (q^3)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin 9, 6 ≤ i.val → z i=z 8) ∧ q.eval (z 8)=0 ∧
      ‖a‖=1 ∧ ‖b‖=1 ∧ (a*starRingEnd ℂ b).re=0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by sorry
