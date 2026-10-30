-- Prove2me | Theorems.Thm_DerivativeChainContinuation_interlacing_transport_identity
-- name    : DerivativeChainContinuation.interlacing_transport_identity
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:11:19.538636+00:00
-- url     : https://prove2.me/theorems/0dbe4cc1-b2f3-4abb-9398-971940d67813
-- title:
--   Exact weighted transport identity for interlacing rows
-- statement:
--   Let $a_0,\ldots,a_m$ and $b_0,\ldots,b_{m-1}$ be real numbers with $a_i\le b_i\le a_{i+1}$. For $D(x)=\sum_j(2j+1-\#x)x_j$,
--
--   $$\sum_{i=0}^{m-1}\bigl((m-i)|b_i-a_i|+(i+1)|a_{i+1}-b_i|\bigr)=D(a)-D(b).$$
--
--   The identity measures the exact dispersion loss of one interlacing step.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteTransport.lean#L30-L52

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.interlacing_transport_identity (m : ℕ) (a : Fin (m+1) → ℝ) (b : Fin m → ℝ)
    (hab : ∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ) :
    (∑ i : Fin m, (((m : ℝ)-i.val)*|b i-a i.castSucc| +
      ((i.val : ℝ)+1)*|a i.succ-b i|)) = orderedDispersion a-orderedDispersion b := by sorry
