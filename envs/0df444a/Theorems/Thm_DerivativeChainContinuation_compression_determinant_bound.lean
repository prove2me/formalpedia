-- Prove2me | Theorems.Thm_DerivativeChainContinuation_compression_determinant_bound
-- name    : DerivativeChainContinuation.compression_determinant_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:53:40.872439+00:00
-- url     : https://prove2.me/theorems/91010627-d7b1-4ebe-a991-d159a62f5c6a
-- title:
--   Root covariance determinant bounded by the deficit
-- statement:
--   Let $a_1,\ldots,a_n$ be centered complex root slots with $n\ge2$ and $|a_i|\le R$. With $p=\prod_i(X-a_i)$, $$\det\Sigma(a)\le2R^2\delta(p).$$ The radius is a genuine bound on every source root.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionDeficit.lean#L68-L99

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.compression_determinant_bound {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) (R : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ R) :
    (covariance a).det ≤ 2*R^2*schoenbergDeficit (∏ i, (X-C (a i))) := by sorry
