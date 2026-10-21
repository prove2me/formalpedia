-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row9_newton_inverse
-- name    : DerivativeChainPrivate.row9_newton_inverse
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T18:55:36.677995+00:00
-- url     : https://prove2.me/theorems/f0a43627-f626-4687-8cb5-590f3d744a36
-- title:
--   Exact inverse certificate for the row-9 inverse cubic
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy
--   $$\alpha^3=\frac{1001}{2}-462\alpha+84\alpha^2.$$
--   Let $P,Q,E,J$ denote the explicit row-9 coefficient polynomials in the fifth-power inverse-certificate bundle, with their dependence on $\alpha$. For every $t\in\mathbb C$,
--   $$1-Q(t)\partial_vG(t,P(t))=t^{32}J(t),$$
--   where
--   $$G_9(t,v)=-2v^3+(168-42t)v^2+(-924+840t-168t^2+4t^3)v+1001-1716t+924t^2-168t^3+7t^4.$$
--   This polynomial identity is an input to the bounded analytic Newton construction for the degree-9 derivative row of a cubic fifth power. It holds for every real root of the displayed cubic, with no floating-point or convergence assumption.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 9. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row9_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row9_newton_inverse (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    1-row9Q α t*(row9G1 t+2*row9G2 t*row9P α t+3*row9G3 t*(row9P α t)^2) = t^32*row9J α t := by sorry
