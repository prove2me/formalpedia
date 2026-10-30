-- Prove2me | Theorems.Thm_DerivativeChainContinuation_compression_gram_cyclic
-- name    : DerivativeChainContinuation.compression_gram_cyclic
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:54:04.936207+00:00
-- url     : https://prove2.me/theorems/66c18fa9-f37a-4dfd-8906-ee02fd6d84a3
-- title:
--   Cyclic determinant form of the regularized root compression
-- statement:
--   For $n>0$, complex slots $a_i$, centering projection $P$ and real $t$, $$\det(tI+B^*B)=\det(tI+\operatorname{diag}(\overline a)P\operatorname{diag}(a)P),\qquad B=P\operatorname{diag}(a)P.$$ This is an identity for arbitrary real $t$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionGramCyclic.lean#L13-L32

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.compression_gram_cyclic {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ) :
    (regularizedGram (rootCompression a) t).det =
      (diagonal (fun _ => (t:ℂ))+
        diagonal (star a)*centeringProjection n*diagonal a*centeringProjection n).det := by sorry
