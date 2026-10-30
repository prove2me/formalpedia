-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
-- name    : DerivativeChainPrivate.cubic_graph_coordinate_parts
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:23:56.611009+00:00
-- url     : https://prove2.me/theorems/63e3522b-22b6-48a7-92dd-1eb4517752cd
-- title:
--   Coordinate decomposition of a cubic inverse graph
-- statement:
--   Let $\beta,z,e\in\mathbb C$, $\alpha,b\in\mathbb R$, $z\ne0$, and $\beta/z=\alpha z^2-b+e/z$. Writing $x=\operatorname{Re}z$, $y=\operatorname{Im}z$,
--
--   $$\operatorname{Re}\beta=x[\alpha(x^2-3y^2)-b]+\operatorname{Re}e,$$\n$$\operatorname{Im}\beta=y[\alpha(3x^2-y^2)-b]+\operatorname{Im}e,$$\n$$\operatorname{Im}(\beta/z)=2\alpha xy+\operatorname{Im}(e/z).$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1156-L1177

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.cubic_graph_coordinate_parts (β z e : ℂ) (α b : ℝ) (hz : z ≠ 0)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+e/z) :
    β.re = z.re * (α*(z.re^2-3*z.im^2)-b)+e.re ∧
      β.im = z.im * (α*(3*z.re^2-z.im^2)-b)+e.im ∧
      (β/z).im = 2*α*z.re*z.im+(e/z).im := by sorry
