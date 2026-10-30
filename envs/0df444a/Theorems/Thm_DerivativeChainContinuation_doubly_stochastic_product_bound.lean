-- Prove2me | Theorems.Thm_DerivativeChainContinuation_doubly_stochastic_product_bound
-- name    : DerivativeChainContinuation.doubly_stochastic_product_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:00:17.528703+00:00
-- url     : https://prove2.me/theorems/62f60382-5f83-4d4b-b742-dcc6f76d6990
-- title:
--   A positive product under a doubly stochastic averaging matrix
-- statement:
--   Let $w_{ij}\ge0$ have every row and column sum equal to one, and let $v_j>0$. Then $$\prod_jv_j\le\prod_i\left(\sum_jw_{ij}v_j\right).$$ This is the finite logarithmic Jensen product inequality.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/StochasticProduct.lean#L19-L37

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.doubly_stochastic_product_bound {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (v : ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j=1)
    (hcol : ∀ j, ∑ i, w i j=1) (hv : ∀ j, 0 < v j) :
    (∏ j, v j) ≤ ∏ i, (∑ j, w i j*v j) := by sorry
