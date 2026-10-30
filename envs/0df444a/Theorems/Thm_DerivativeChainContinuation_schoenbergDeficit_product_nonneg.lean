-- Prove2me | Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_product_nonneg
-- name    : DerivativeChainContinuation.schoenbergDeficit_product_nonneg
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:30:49.905607+00:00
-- url     : https://prove2.me/theorems/032b43af-f6f2-4c40-a611-648d1acd08b8
-- title:
--   Nonnegative Schoenberg deficit for a centered root product
-- statement:
--   Let $p(X)=\prod_{i=1}^n(X-a_i)$ with $n\ge2$ and $\sum_i a_i=0$. If $q$ is the monic normalized derivative and $V$ denotes the uniform squared root norm, then $$\delta(p)=(n-2)V(p)-(n-1)V(q)\ge0.$$ Multiplicities are allowed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchoenbergDeficit.lean#L29-L51

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.schoenbergDeficit_product_nonneg {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    0 ≤ schoenbergDeficit (∏ i, (X-C (a i))) := by sorry
