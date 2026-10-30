-- Prove2me | Theorems.Thm_DerivativeChainContinuation_all_scale_product_loss
-- name    : DerivativeChainContinuation.all_scale_product_loss
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:51:32.492311+00:00
-- url     : https://prove2.me/theorems/411373d8-1e89-4eac-8654-da0d6e1dc623
-- title:
--   Relative product loss at every positive scale
-- statement:
--   For finite real families $d_i,q_i$, assume $t>0$, $g>0$, $d_i\ge t$, $q_i\ge0$ and $g\le\prod_i(d_i+q_i)$. Then $$1-\frac{\prod_i d_i}{g}\le\min\left(1,\frac{\sum_iq_i}{t}\right).$$ There is no restriction that $t$ exceed the total increment.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AllScaleProductBound.lean#L6-L36

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.all_scale_product_loss {ι : Type*} [Fintype ι]
    (d q : ι → ℝ) (t g : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hd : ∀ i,t ≤ d i) (hq : ∀ i,0 ≤ q i)
    (hupper : g ≤ ∏ i,(d i+q i)) :
    1-(∏ i,d i)/g ≤ min 1 ((∑ i,q i)/t) := by sorry
