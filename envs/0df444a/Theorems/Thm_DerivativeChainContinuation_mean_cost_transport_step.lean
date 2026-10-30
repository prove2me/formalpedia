-- Prove2me | Theorems.Thm_DerivativeChainContinuation_mean_cost_transport_step
-- name    : DerivativeChainContinuation.mean_cost_transport_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:13:19.470323+00:00
-- url     : https://prove2.me/theorems/4412bd14-b8e3-4754-b8e3-8a570cb252e0
-- title:
--   Mean transport cost across one interlacing step
-- statement:
--   Let $m>0$ and let real rows $a_0,\ldots,a_m$ and $b_0,\ldots,b_{m-1}$ interlace. Suppose real costs satisfy $A_i\le B_i+|b_i-a_i|$ and $A_{i+1}\le B_i+|a_{i+1}-b_i|$ for every $i<m$. Then
--
--   $$\frac{\sum_j A_j}{m+1}\le\frac{\sum_i B_i}{m}+\frac{D(a)-D(b)}{m(m+1)},$$
--
--   where $D$ is ordered dispersion. This is the averaging inequality used to telescope row-history costs.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteTransport.lean#L54-L91

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.mean_cost_transport_step (m : ℕ) (hm : 0 < m)
    (a : Fin (m+1) → ℝ) (b : Fin m → ℝ)
    (A : Fin (m+1) → ℝ) (B : Fin m → ℝ)
    (hab : ∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hleft : ∀ i, A i.castSucc ≤ B i+|b i-a i.castSucc|)
    (hright : ∀ i, A i.succ ≤ B i+|a i.succ-b i|) :
    (∑ j, A j)/(m+1 : ℝ) ≤ (∑ i, B i)/(m : ℝ) +
      (orderedDispersion a-orderedDispersion b)/((m : ℝ)*(m+1)) := by sorry
