-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
-- name    : DerivativeChainContinuation.finite_weighted_variance
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:40:27.037933+00:00
-- url     : https://prove2.me/theorems/e683073d-1e26-424c-8fc8-fafe1013ee66
-- title:
--   Finite complex weighted variance decomposition
-- statement:
--   Let finite real weights satisfy $\sum_iw_i=1$ and $\sum_iw_iv_i=z$ for complex points $v_i$. For every reference point $u$, $$\sum_iw_i|v_i-u|^2=|z-u|^2+\sum_iw_i|v_i-z|^2.$$ The identity also holds for signed real weights.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteWeightedVariance.lean#L6-L21

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.finite_weighted_variance {ι : Type} [Fintype ι]
    (w : ι → ℝ) (v : ι → ℂ) (z u : ℂ) (hs : ∑ i, w i=1)
    (hm : ∑ i, (w i:ℂ)*v i=z) :
    (∑ i, w i*‖v i-u‖^2)=‖z-u‖^2+(∑ i, w i*‖v i-z‖^2) := by sorry
