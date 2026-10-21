-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row10_newton_residual
-- name    : DerivativeChainPrivate.row10_newton_residual
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T18:55:31.65129+00:00
-- url     : https://prove2.me/theorems/94b0b9b2-4fbd-4f04-a132-2d14a781a916
-- title:
--   Exact residual certificate for the row-10 inverse cubic
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy
--   $$\alpha^3=\frac{1001}{20}-66\alpha+21\alpha^2.$$
--   Let $P,Q,E,J$ denote the explicit row-10 coefficient polynomials in the fifth-power inverse-certificate bundle, with their dependence on $\alpha$. For every $t\in\mathbb C$,
--   $$G(t,P(t))=t^{32}E(t),$$
--   where
--   $$G_{10}(t,v)=-60v^3+(1260-630t+30t^2)v^2+(-3960+5040t-1680t^2+120t^3)v+3003-6435t+4620t^2-1260t^3+105t^4-t^5.$$
--   This polynomial identity is an input to the bounded analytic Newton construction for the degree-10 derivative row of a cubic fifth power. It holds for every real root of the displayed cubic, with no floating-point or convergence assumption.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 10. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_residual
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row10_newton_residual (α : ℝ)
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) (t : ℂ) :
    row10G0 t+row10G1 t*row10P α t+row10G2 t*(row10P α t)^2+row10G3 t*(row10P α t)^3 = t^32*row10E α t := by sorry
