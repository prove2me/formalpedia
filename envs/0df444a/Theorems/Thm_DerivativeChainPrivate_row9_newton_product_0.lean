-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row9_newton_product_0
-- name    : DerivativeChainPrivate.row9_newton_product_0
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T20:43:21.148905+00:00
-- url     : https://prove2.me/theorems/c59a40f0-0e0a-4bc7-b974-a3c2a8b9d4bd
-- title:
--   Exact row-9 multiplier product for square-coefficient block 0
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy $$\alpha^3=\frac{1001}{2}-462\alpha+84\alpha^2.$$ Let $Q_\alpha$ be the explicit Newton multiplier polynomial and let $S_{\alpha,0}$ be the polynomial formed from coefficients 0 through 15 of the reduced square polynomial, shifted to begin at exponent zero. Let $U_{\alpha,0}$ be the explicit reduced-product polynomial in the corresponding definition file. For every $t\in\mathbb C$,
--   $$Q_\alpha(t)S_{\alpha,0}(t)=U_{\alpha,0}(t).$$
--   The four adjacent blocks cover the entire square polynomial. These identities permit exact verification of the inverse residual in bounded arithmetic stages.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 9. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_product0
import Definitions.Def_DerivativeChainPrivate_fifth_row9_square
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row9_newton_product_0 (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    row9Q α t*row9SBlock0 α t=row9U0 α t := by sorry
