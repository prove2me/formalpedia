-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_power_sharp_disk
-- name    : DerivativeChainContinuation.normalized_power_sharp_disk
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:53:46.613718+00:00
-- url     : https://prove2.me/theorems/bf7e33e5-fcc9-4d8f-bd48-d10c9d2efb57
-- title:
--   Conditional sharp disk budget for a normalized cubic power
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Write $\rho_\star=(1+\sqrt{10})/3$. Fix an integer $h>0$ and real $a,b\ge0$. Put $p_\beta(X)=(X^3-aX-b\beta)^h$ and $N=3h$. Assume that for every $\operatorname{Re}\beta\ge0$, $\operatorname{Im}\beta>0$ there is $z\in\mathbb C^N$ satisfying $p_\beta^{(N-i-1)}(z_i)=0$, $z_0=0$, a constant suffix $z_i=z_{N-1}$ for $i\ge2h$, and nondecreasing real and imaginary coordinates. For any $\beta$ with $\operatorname{Re}\beta\ge0$, if every root of $X^3-aX-b\beta$ lies in a disk of center $o$ and radius $R\ge0$, there is a complete $N$-entry root list starting at zero, constant from index $2h$, and ending at a base-cubic root. It admits unit orthogonal frames with nondecreasing projections and satisfies $L(z)\le\rho_\star R$. No unrestricted strict-chain existence statement is supplied by this conditional theorem.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpNormalizedPower.lean#L8-L75

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.normalized_power_sharp_disk (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (β : ℂ) (hβR : 0 ≤ β.re) (o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z : ℂ, (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval z=0 → ‖z-o‖ ≤ R) :
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by sorry
