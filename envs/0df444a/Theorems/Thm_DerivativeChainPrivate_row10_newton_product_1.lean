-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row10_newton_product_1
-- name    : DerivativeChainPrivate.row10_newton_product_1
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T20:46:45.163256+00:00
-- url     : https://prove2.me/theorems/5d8b0de7-b4ef-4af1-908f-fa01da8a2ff0
-- title:
--   Exact row-10 multiplier product for square-coefficient block 1
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy $$\alpha^3=\frac{1001}{20}-66\alpha+21\alpha^2.$$ Let $Q_\alpha$ be the explicit Newton multiplier polynomial and let $S_{\alpha,1}$ be the polynomial formed from coefficients 16 through 31 of the reduced square polynomial, shifted to begin at exponent zero. Let $U_{\alpha,1}$ be the explicit reduced-product polynomial in the corresponding definition file. For every $t\in\mathbb C$,
--   $$Q_\alpha(t)S_{\alpha,1}(t)=U_{\alpha,1}(t).$$
--   The four adjacent blocks cover the entire square polynomial. These identities permit exact verification of the inverse residual in bounded arithmetic stages.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 10. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_product1
import Definitions.Def_DerivativeChainPrivate_fifth_row10_square
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row10_newton_product_1 (α : ℝ)
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) (t : ℂ) :
    row10Q α t*row10SBlock1 α t=row10U1 α t := by sorry
