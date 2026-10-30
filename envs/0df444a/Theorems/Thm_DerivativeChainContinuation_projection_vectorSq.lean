-- Prove2me | Theorems.Thm_DerivativeChainContinuation_projection_vectorSq
-- name    : DerivativeChainContinuation.projection_vectorSq
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:46:27.059017+00:00
-- url     : https://prove2.me/theorems/8efab374-14a3-4eea-aaed-082eecf3e9c3
-- title:
--   Exact squared norm after centering projection
-- statement:
--   For $n>0$, $v\in\mathbb C^n$, and $P=I-\mathbf1\mathbf1^*/n$, $$\|Pv\|^2=\|v\|^2-\frac1n\left|\sum_i v_i\right|^2.$$ This is the orthogonal projection onto the zero-sum subspace.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/MatrixEnergy.lean#L25-L40

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_MatrixEnergy
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.projection_vectorSq {n : ℕ} (hn : n ≠ 0) (v : Fin n → ℂ) :
    vectorSq (centeringProjection n *ᵥ v) =
      vectorSq v - Complex.normSq (∑ i, v i)/(n : ℝ) := by sorry
