-- Prove2me | Theorems.Thm_DerivativeChainContinuation_rootCompression_commutator_norm
-- name    : DerivativeChainContinuation.rootCompression_commutator_norm
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:50:50.084238+00:00
-- url     : https://prove2.me/theorems/c8715200-8e89-4732-9b93-ed57d021265c
-- title:
--   Compression commutator and covariance determinant
-- statement:
--   For centered complex root slots $a_1,\ldots,a_n$ with $n>0$, let $B$ be their ambient compression and $\Sigma$ their real two-dimensional covariance. Then $$\|BB^*-B^*B\|_F^2=8\det\Sigma.$$ This is the exact nonnormality identity C3.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionNorms.lean#L6-L31

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.rootCompression_commutator_norm {n : ℕ} (hn : n ≠ 0)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    frobeniusSq (rootCompression a * (rootCompression a).conjTranspose -
      (rootCompression a).conjTranspose * rootCompression a) = 8*(covariance a).det := by sorry
