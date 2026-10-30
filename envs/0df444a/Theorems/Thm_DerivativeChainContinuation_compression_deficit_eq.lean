-- Prove2me | Theorems.Thm_DerivativeChainContinuation_compression_deficit_eq
-- name    : DerivativeChainContinuation.compression_deficit_eq
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:43:58.464611+00:00
-- url     : https://prove2.me/theorems/14a9cdd2-4032-40e6-87f9-256993753f70
-- title:
--   The polynomial deficit equals compression energy loss
-- statement:
--   For centered root slots $a_1,\ldots,a_n$ with $n\ge2$, let $p=\prod_i(X-a_i)$ and $B$ be the ambient root compression. Then $$\delta(p)=\|B\|_F^2-\sum_{\lambda\in Z(\chi_B)}|\lambda|^2.$$ The spectrum counts multiplicities and includes the additional zero.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionDeficit.lean#L20-L41

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.compression_deficit_eq {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    schoenbergDeficit (∏ i, (X-C (a i))) = frobeniusSq (rootCompression a) -
      ((rootCompression a).charpoly.roots.map Complex.normSq).sum := by sorry
