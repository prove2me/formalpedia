-- Prove2me | Theorems.Thm_DerivativeChainContinuation_all_scale_product_exp
-- name    : DerivativeChainContinuation.all_scale_product_exp
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:47:23.013575+00:00
-- url     : https://prove2.me/theorems/53df37d2-c5f9-4941-a23c-437dd17e6466
-- title:
--   Exponential upper estimate for a positive-scale product
-- statement:
--   For finite real families $d_i,q_i$, assume $t>0$, $d_i\ge t$, $q_i\ge0$ and $g\le\prod_i(d_i+q_i)$. Then $$g\le\left(\prod_i d_i\right)\exp\left(\frac{\sum_iq_i}{t}\right).$$ No sign assumption on $g$ is needed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AllScaleExponential.lean#L7-L29

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators

theorem DerivativeChainContinuation.all_scale_product_exp {ι : Type*} [Fintype ι]
    (d q : ι → ℝ) (t g : ℝ) (ht : 0 < t)
    (hd : ∀ i,t ≤ d i) (hq : ∀ i,0 ≤ q i)
    (hupper : g ≤ ∏ i,(d i+q i)) :
    g ≤ (∏ i,d i)*Real.exp ((∑ i,q i)/t) := by sorry
