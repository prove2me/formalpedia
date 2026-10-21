-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row9_newton_square
-- name    : DerivativeChainPrivate.row9_newton_square
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T19:36:50.120355+00:00
-- url     : https://prove2.me/theorems/ac61bc57-2f90-47f2-95fb-43dd4265f037
-- title:
--   Exact reduced square certificate for the row-9 Newton polynomial
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy $$\alpha^3=\frac{1001}{2}-462\alpha+84\alpha^2.$$ Let $P_\alpha(t)$ be the explicit degree-at-most-31 Newton approximant for the row-9 inverse cubic, and let $S_\alpha(t)$ be the degree-at-most-62 coefficient polynomial in the reduced-square definition bundle. Then, for every $t\in\mathbb C$,
--   $$P_\alpha(t)^2=S_\alpha(t).$$
--   The coefficient expressions are rational quadratic polynomials in $\alpha$. This exact algebraic identity controls the size of the later residual and inverse-derivative calculations without changing their statements.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 9. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_square
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row9_newton_square (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    (row9P α t)^2=row9S α t := by sorry
