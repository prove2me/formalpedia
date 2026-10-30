-- Prove2me | Theorems.Thm_DerivativeChainContinuation_rootCompression_energy
-- name    : DerivativeChainContinuation.rootCompression_energy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:28:46.219983+00:00
-- url     : https://prove2.me/theorems/c2079dc9-4933-44ad-b1ec-c5e1163a954c
-- title:
--   Frobenius energy of a centered root compression
-- statement:
--   For $n>0$ and complex root slots $a_1,\ldots,a_n$ with $\sum_i a_i=0$, let $B=P\operatorname{diag}(a)P$ and $V=n^{-1}\sum_i|a_i|^2$. Then $$\|B\|_F^2=(n-2)V.$$ The ambient compression retains one zero eigenvalue.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionEnergy.lean#L7-L40

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

theorem DerivativeChainContinuation.rootCompression_energy {n : ℕ} (hn : n ≠ 0)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    frobeniusSq (rootCompression a) = ((n : ℝ)-2)*secondMoment a := by sorry
