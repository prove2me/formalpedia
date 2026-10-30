-- Prove2me | Theorems.Thm_DerivativeChainContinuation_rank_two_determinant
-- name    : DerivativeChainContinuation.rank_two_determinant
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:56:09.063995+00:00
-- url     : https://prove2.me/theorems/1b8c221e-dd8a-459c-a036-20cbbe3f268a
-- title:
--   Exact diagonal plus rank-two determinant identity
-- statement:
--   Let $D=\operatorname{diag}(d)$ be an invertible finite complex diagonal matrix, and let $U$ have columns $u,v$ and $V$ have rows $s,t$. Then $$\det(D+UV)=\det(D)\det(I_2+VD^{-1}U).$$ The formal statement expands the two-by-two determinant into its four finite sums.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RankTwoDeterminant.lean#L8-L26

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators

theorem DerivativeChainContinuation.rank_two_determinant {n : ℕ} (d u v s t : Fin n → ℂ)
    (hd : ∀ i,d i ≠ 0) :
    (diagonal d + Matrix.of (fun i j : Fin n => u i*s j+v i*t j)).det =
      (∏ i,d i)*((1+∑ i,s i*u i/d i)*(1+∑ i,t i*v i/d i)-
        (∑ i,s i*v i/d i)*(∑ i,t i*u i/d i)) := by sorry
