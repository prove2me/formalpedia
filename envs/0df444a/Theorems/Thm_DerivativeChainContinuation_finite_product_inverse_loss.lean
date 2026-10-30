-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_product_inverse_loss
-- name    : DerivativeChainContinuation.finite_product_inverse_loss
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:49:32.963925+00:00
-- url     : https://prove2.me/theorems/1910f27e-833f-40c2-aa71-806d8509b96c
-- title:
--   Loss of the reciprocal of a finite positive product
-- statement:
--   For a finite set $S$ and numbers $x_i\ge0$ on $S$, $$0\le1-\left(\prod_{i\in S}(1+x_i)\right)^{-1}\le\min\left(1,\sum_{i\in S}x_i\right).$$ The empty set is included.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ProductLoss.lean#L6-L31

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.finite_product_inverse_loss {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ 1-(∏ i ∈ s, (1+x i))⁻¹ ∧
    1-(∏ i ∈ s, (1+x i))⁻¹ ≤ min 1 (∑ i ∈ s, x i) := by sorry
