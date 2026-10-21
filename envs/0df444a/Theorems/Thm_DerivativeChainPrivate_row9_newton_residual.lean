-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row9_newton_residual
-- name    : DerivativeChainPrivate.row9_newton_residual
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T18:55:35.103623+00:00
-- url     : https://prove2.me/theorems/528b13d0-74fd-4ad1-b227-3b3236b86fbb
-- title:
--   Exact residual certificate for the row-9 inverse cubic
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy
--   $$\alpha^3=\frac{1001}{2}-462\alpha+84\alpha^2.$$
--   Let $P,Q,E,J$ denote the explicit row-9 coefficient polynomials in the fifth-power inverse-certificate bundle, with their dependence on $\alpha$. For every $t\in\mathbb C$,
--   $$G(t,P(t))=t^{32}E(t),$$
--   where
--   $$G_9(t,v)=-2v^3+(168-42t)v^2+(-924+840t-168t^2+4t^3)v+1001-1716t+924t^2-168t^3+7t^4.$$
--   This polynomial identity is an input to the bounded analytic Newton construction for the degree-9 derivative row of a cubic fifth power. It holds for every real root of the displayed cubic, with no floating-point or convergence assumption.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 9. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_residual
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row9_newton_residual (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    row9G0 t+row9G1 t*row9P α t+row9G2 t*(row9P α t)^2+row9G3 t*(row9P α t)^3 = t^32*row9E α t := by sorry
