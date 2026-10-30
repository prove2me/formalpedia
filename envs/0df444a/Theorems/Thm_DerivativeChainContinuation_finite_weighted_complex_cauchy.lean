-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_weighted_complex_cauchy
-- name    : DerivativeChainContinuation.finite_weighted_complex_cauchy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:14:25.317627+00:00
-- url     : https://prove2.me/theorems/90058ff9-a859-4dd7-a99e-8b64741cb61f
-- title:
--   Complex Cauchy inequality with nonnegative finite weights
-- statement:
--   For $w_i\ge0$ and complex $a_i$, $$\left|\sum_iw_i a_i\right|^2\le\left(\sum_iw_i\right)\left(\sum_iw_i|a_i|^2\right).$$ No normalization is assumed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteComplexCauchy.lean#L6-L22

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.finite_weighted_complex_cauchy {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → ℂ) (hw : ∀ i,0 ≤ w i) :
    Complex.normSq (∑ i,(w i:ℂ)*a i) ≤ (∑ i,w i)*(∑ i,w i*Complex.normSq (a i)) := by sorry
