-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sharp_cubic_endpoint_attained
-- name    : DerivativeChainContinuation.sharp_cubic_endpoint_attained
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:51:37.149299+00:00
-- url     : https://prove2.me/theorems/c7fe8364-2dd9-41d3-b15a-460de676aa0a
-- title:
--   The normalized cubic endpoint coefficient is attained
-- statement:
--   Write $\rho_\star=(1+\sqrt{10})/3$. There exist real $A\ge0$, $R>0$ and complex $B,a,o$ with $B,a$ in the closed first quadrant, such that $a^3-Aa-B=0$, every root of $z^3-Az-B$ lies in the disk of center $o$ and radius $R$, and
--
--   $$\operatorname{Re}a+\operatorname{Im}a=\rho_\star R.$$
--
--   This is attainment of the endpoint inequality for an actual cubic and a selected endpoint.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicOptimality.lean#L6-L60

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.sharp_cubic_endpoint_attained :
    ∃ (A R : ℝ) (B a o : ℂ), 0 ≤ A ∧ 0 < R ∧ 0 ≤ B.re ∧ 0 ≤ B.im ∧
      0 ≤ a.re ∧ 0 ≤ a.im ∧ a^3-(A:ℂ)*a-B=0 ∧
      (∀ z : ℂ, z^3-(A:ℂ)*z-B=0 → ‖z-o‖ ≤ R) ∧
      a.re+a.im=sharpCubicConstant*R := by sorry
