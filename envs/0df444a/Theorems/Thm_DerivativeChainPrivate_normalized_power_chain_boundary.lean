-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_power_chain_boundary
-- name    : DerivativeChainPrivate.normalized_power_chain_boundary
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:50:44.8259+00:00
-- url     : https://prove2.me/theorems/ee7aa03e-48c4-4686-9c85-c354f5b81403
-- title:
--   Conditional extension of normalized chains to the real parameter boundary
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Fix an integer $h>0$ and real $a,b\ge0$. Put $p_\beta(X)=(X^3-aX-b\beta)^h$ and $N=3h$. Assume that for every $\operatorname{Re}\beta\ge0$, $\operatorname{Im}\beta>0$ there is $z\in\mathbb C^N$ satisfying $p_\beta^{(N-i-1)}(z_i)=0$, $z_0=0$, a constant suffix $z_i=z_{N-1}$ for $i\ge2h$, and nondecreasing real and imaginary coordinates. Then for every $\beta$ with both coordinates nonnegative there is such a list, with $z_{N-1}^3-az_{N-1}-b\beta=0$ and $L(z)\le\sqrt2\,|z_{N-1}|$. The existence hypothesis for the strict upper quadrant is retained.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/NormalizedBoundary.lean#L31-L100

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_power_chain_boundary (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z last‖ := by sorry
