-- Prove2me | Theorems.Thm_DerivativeChainContinuation_uniform_endpoint_second_moment
-- name    : DerivativeChainContinuation.uniform_endpoint_second_moment
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:29:28.116183+00:00
-- url     : https://prove2.me/theorems/6b4837e2-3cf6-4be1-ab32-32593504db2e
-- title:
--   Second moment of a nonnegative Lipschitz endpoint cost
-- statement:
--   Let $n>0$, $x_1,\ldots,x_n\in\mathbb R$ with $\sum_i x_i=0$, and let $f_i\ge0$ satisfy $|f_i-f_j|\le|x_i-x_j|$. If $B\ge0$ and the mean cost is at most $B$ times the root-mean-square position, then
--
--   $$\frac1n\sum_i f_i^2\le(1+B^2)\frac1n\sum_i x_i^2.$$
--
--   This combines a variance estimate with the mean transport bound to obtain the constant $28/3$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/EndpointVariance.lean#L26-L47

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.uniform_endpoint_second_moment (n : ℕ) (hn : 0 < n)
    (x f : Fin n → ℝ) (hcenter : ∑ i, x i = 0)
    (hcost : ∀ i, 0 ≤ f i)
    (hlip : ∀ i j, |f i-f j| ≤ |x i-x j|)
    (B : ℝ) (hB : 0 ≤ B)
    (hmean : (∑ i, f i)/(n : ℝ) ≤ B*Real.sqrt ((∑ i, (x i)^2)/(n : ℝ))) :
    (∑ i, (f i)^2)/(n : ℝ) ≤ (1+B^2)*((∑ i, (x i)^2)/(n : ℝ)) := by sorry
