-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sharp_normalized_cubic_endpoint
-- name    : DerivativeChainContinuation.sharp_normalized_cubic_endpoint
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:34:11.674579+00:00
-- url     : https://prove2.me/theorems/7ef3204b-519a-4175-aed8-24889641975c
-- title:
--   Sharp coordinate sum for a normalized cubic root
-- statement:
--   Write $\rho_\star=(1+\sqrt{10})/3$. Let $A\ge0$, let $B\in\mathbb C$ have nonnegative real and imaginary parts, and let $a\in\mathbb C$ have nonnegative coordinates with $a^3-Aa-B=0$. If every root of $z^3-Az-B$ lies in the closed disk of center $o\in\mathbb C$ and radius $R\ge0$, then
--
--   $$\operatorname{Re}a+\operatorname{Im}a\le\rho_\star R.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicEndpoint.lean#L7-L62

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.sharp_normalized_cubic_endpoint (A : ℝ) (hA : 0 ≤ A) (B a o : ℂ)
    (hBR : 0 ≤ B.re) (hBI : 0 ≤ B.im) (ha : a^3-(A:ℂ)*a-B=0)
    (hx : 0 ≤ a.re) (hy : 0 ≤ a.im) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z : ℂ, z^3-(A:ℂ)*z-B=0 → ‖z-o‖ ≤ R) :
    a.re+a.im ≤ sharpCubicConstant*R := by sorry
