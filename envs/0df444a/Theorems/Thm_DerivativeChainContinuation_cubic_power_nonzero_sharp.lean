-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubic_power_nonzero_sharp
-- name    : DerivativeChainContinuation.cubic_power_nonzero_sharp
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:01:56.755074+00:00
-- url     : https://prove2.me/theorems/ce700d69-3625-45dd-88f9-bbeca5f5c207
-- title:
--   Conditional sharp power-chain budget for a nonzero-moment triple
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Write $\rho_\star=(1+\sqrt{10})/3$. For a triple $u,v,w$ put $m=(u+v+w)/3$ and $D=(u^2+v^2+w^2-uv-uw-vw)/3$. Fix an integer $h>0$ and real $a,b\ge0$. Put $p_\beta(X)=(X^3-aX-b\beta)^h$ and $N=3h$. Assume that for every $\operatorname{Re}\beta\ge0$, $\operatorname{Im}\beta>0$ there is $z\in\mathbb C^N$ satisfying $p_\beta^{(N-i-1)}(z_i)=0$, $z_0=0$, a constant suffix $z_i=z_{N-1}$ for $i\ge2h$, and nondecreasing real and imaginary coordinates. Here require $a,b>0$. If $u,v,w$ lie in the disk of center $o$ and real radius $R$, and $D\ne0$, put $q(X)=(X-u)(X-v)(X-w)$. The resulting list starts at the centroid, satisfies the roots of $q^h$ in derivative orders $3h-i-1$, has constant suffix from index $2h$, and ends at a root of $q$. It has two unit orthogonal frame coefficients $A,B$, meaning $\operatorname{Re}(A\overline B)=0$, for which both sequences $\operatorname{Re}(Az_i)$ and $\operatorname{Re}(Bz_i)$ are nondecreasing, and $L(z)\le\rho_\star R$. The strict normalized-chain hypothesis remains an input.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpPowerNonzero.lean#L8-L63

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.cubic_power_nonzero_sharp (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (u v w o : ℂ) (R : ℝ) (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by sorry
