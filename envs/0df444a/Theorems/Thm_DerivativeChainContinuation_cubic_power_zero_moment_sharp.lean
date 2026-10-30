-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubic_power_zero_moment_sharp
-- name    : DerivativeChainContinuation.cubic_power_zero_moment_sharp
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:09:44.898666+00:00
-- url     : https://prove2.me/theorems/872f937a-a6be-436d-936f-8003c00eb68b
-- title:
--   Conditional extension of a sharp power-chain bound to zero moment
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Write $\rho_\star=(1+\sqrt{10})/3$. For a triple $u,v,w$ put $m=(u+v+w)/3$ and $D=(u^2+v^2+w^2-uv-uw-vw)/3$. Fix $h>0$. Suppose for every nonzero-$D$ triple in any containing disk, the conclusion below is already available. For a zero-$D$ triple $u,v,w$ in a disk of center $o$ and radius $R\ge0$, put $q(X)=(X-u)(X-v)(X-w)$. The resulting list starts at the centroid, satisfies the roots of $q^h$ in derivative orders $3h-i-1$, has constant suffix from index $2h$, and ends at a root of $q$. It has two unit orthogonal frame coefficients $A,B$, meaning $\operatorname{Re}(A\overline B)=0$, for which both sequences $\operatorname{Re}(Az_i)$ and $\operatorname{Re}(Bz_i)$ are nondecreasing, and $L(z)\le\rho_\star R$. This theorem retains the universal nonzero-moment result as a hypothesis.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpPowerZero.lean#L9-L133

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.cubic_power_zero_moment_sharp (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hnonzero : ∀ u v w o : ℂ, ∀ R : ℝ, ‖u-o‖ ≤ R → ‖v-o‖ ≤ R → ‖w-o‖ ≤ R →
      (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0 →
      let q := (X-C u)*(X-C v)*(X-C w)
      ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
        (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
        z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
        ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
        Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
        chainCost z ≤ sharpCubicConstant*R)
    (u v w o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3=0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by sorry
