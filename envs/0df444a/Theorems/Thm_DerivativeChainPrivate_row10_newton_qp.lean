-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row10_newton_qp
-- name    : DerivativeChainPrivate.row10_newton_qp
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T20:43:13.307217+00:00
-- url     : https://prove2.me/theorems/4a595c78-3f1f-45ce-be62-5518685e920a
-- title:
--   Exact product of the row-10 Newton multiplier and approximant
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy $$\alpha^3=\frac{1001}{20}-66\alpha+21\alpha^2.$$ Let $P_\alpha,Q_\alpha$ be the explicit degree-at-most-31 Newton polynomials for the row-10 inverse cubic, and let $V_\alpha$ be the explicit reduced-product polynomial. Then, for every $t\in\mathbb C$,
--   $$Q_\alpha(t)P_\alpha(t)=V_\alpha(t).$$
--   All coefficient expressions are rational quadratic polynomials in $\alpha$. This identity is a reusable arithmetic stage in the inverse-derivative residual certificate.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 10. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_qp
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row10_newton_qp (α : ℝ)
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) (t : ℂ) :
    row10Q α t*row10P α t=row10V α t := by sorry
