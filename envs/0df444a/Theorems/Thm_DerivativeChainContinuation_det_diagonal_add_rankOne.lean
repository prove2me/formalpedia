-- Prove2me | Theorems.Thm_DerivativeChainContinuation_det_diagonal_add_rankOne
-- name    : DerivativeChainContinuation.det_diagonal_add_rankOne
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:13:52.52698+00:00
-- url     : https://prove2.me/theorems/f238afc5-741d-43bf-a971-182f984011b0
-- title:
--   Determinant of a diagonal matrix plus a rank-one matrix
-- statement:
--   For complex vectors $d,u,v$ indexed by $\{1,\ldots,n\}$, assume every $d_i\ne0$. Then $$\det(\operatorname{diag}(d)+uv^T)=\Bigl(\prod_i d_i\Bigr)\Bigl(1+\sum_i v_i u_i/d_i\Bigr).$$ This classical determinant identity is used to identify the differentiator compression.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionPolynomial.lean#L9-L31

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.det_diagonal_add_rankOne {n : ℕ} (d u v : Fin n → ℂ)
    (hd : ∀ i, d i ≠ 0) :
    (diagonal d + vecMulVec u v).det = (∏ i, d i)*(1+∑ i, v i*u i/d i) := by sorry
