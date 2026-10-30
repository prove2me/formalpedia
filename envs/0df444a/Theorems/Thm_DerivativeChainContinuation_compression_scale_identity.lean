-- Prove2me | Theorems.Thm_DerivativeChainContinuation_compression_scale_identity
-- name    : DerivativeChainContinuation.compression_scale_identity
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:58:20.109003+00:00
-- url     : https://prove2.me/theorems/0e725281-79f0-4201-87d2-c40439897143
-- title:
--   Exact all-scale Gram determinant identity for root compression
-- statement:
--   For $n>0$, complex slots $a_i$ and $t>0$, put $d_i=t+|a_i|^2$, $D=\prod_i d_i$, $M_0=n^{-1}\sum_i d_i^{-1}$, $M_1=n^{-1}\sum_i a_i/d_i$ and $F=tM_0^2+|M_1|^2$. For the ambient root compression $B$, $$\det(tI+B^*B)=tDF.$$ No source-centering assumption is imposed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionScaleIdentity.lean#L10-L73

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators

theorem DerivativeChainContinuation.compression_scale_identity {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ)
    (ht : 0 < t) :
    let d := fun i => (t:ℂ)+(Complex.normSq (a i):ℂ);
    (regularizedGram (rootCompression a) t).det =
      (∏ i,d i)*((t:ℂ)/(n:ℂ)^2)*
        ((t:ℂ)*(∑ i,(d i)⁻¹)^2+(∑ i,a i/d i)*(∑ i,star (a i)/d i)) := by sorry
