-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubic_power_sharp_radius_of_strict_normalized_chain
-- name    : DerivativeChainContinuation.cubic_power_sharp_radius_of_strict_normalized_chain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:13:05.300511+00:00
-- url     : https://prove2.me/theorems/8aedb5e6-10fd-4ba4-a162-377123d41f67
-- title:
--   Conditional transfer from normalized chains to every monic cubic
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Write $\rho_\star=(1+\sqrt{10})/3$. Fix an integer $h>0$ and real $a,b\ge0$. Put $p_\beta(X)=(X^3-aX-b\beta)^h$ and $N=3h$. Assume that for every $\operatorname{Re}\beta\ge0$, $\operatorname{Im}\beta>0$ there is $z\in\mathbb C^N$ satisfying $p_\beta^{(N-i-1)}(z_i)=0$, $z_0=0$, a constant suffix $z_i=z_{N-1}$ for $i\ge2h$, and nondecreasing real and imaginary coordinates. Here require $a,b>0$. For any monic complex cubic $q$, if all its roots lie in a disk of center $o$ and radius $R\ge0$, The resulting list starts at the centroid, satisfies the roots of $q^h$ in derivative orders $3h-i-1$, has constant suffix from index $2h$, and ends at a root of $q$. It has two unit orthogonal frame coefficients $A,B$, meaning $\operatorname{Re}(A\overline B)=0$, for which both sequences $\operatorname{Re}(Az_i)$ and $\operatorname{Re}(Bz_i)$ are nondecreasing, and $L(z)\le\rho_\star R$. The centroid is $q.\mathrm{roots}.\mathrm{sum}/3$, counting multiplicity. The incoming strict normalized-chain existence hypothesis is explicit; this does not prove complete chains for arbitrary powers by itself.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpPowerRadius.lean#L9-L40

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.cubic_power_sharp_radius_of_strict_normalized_chain (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree=3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x=0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by sorry
