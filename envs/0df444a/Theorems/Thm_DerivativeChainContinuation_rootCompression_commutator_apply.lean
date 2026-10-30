-- Prove2me | Theorems.Thm_DerivativeChainContinuation_rootCompression_commutator_apply
-- name    : DerivativeChainContinuation.rootCompression_commutator_apply
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:48:34.869539+00:00
-- url     : https://prove2.me/theorems/c33b89be-2b63-432f-8e67-f7f603bf406d
-- title:
--   Entries of the root compression commutator
-- statement:
--   For $n>0$ and centered complex root slots $a_i$, let $B=P\operatorname{diag}(a)P$. Then $$[B,B^*]_{ij}=\frac{\overline{a_i}a_j-a_i\overline{a_j}}n.$$ No spectral hypothesis is required.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionGeometry.lean#L54-L92

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.rootCompression_commutator_apply {n : ℕ} (hn : n ≠ 0)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) (i j : Fin n) :
    (rootCompression a * (rootCompression a).conjTranspose -
      (rootCompression a).conjTranspose * rootCompression a) i j =
      (star (a i)*a j-a i*star (a j))/(n : ℂ) := by sorry
