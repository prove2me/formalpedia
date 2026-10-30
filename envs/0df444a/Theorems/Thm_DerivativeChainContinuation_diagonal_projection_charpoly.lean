-- Prove2me | Theorems.Thm_DerivativeChainContinuation_diagonal_projection_charpoly
-- name    : DerivativeChainContinuation.diagonal_projection_charpoly
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:15:52.545993+00:00
-- url     : https://prove2.me/theorems/565fc572-057e-4dd8-9fed-ef3bd48f4194
-- title:
--   Characteristic polynomial of the differentiator projection
-- statement:
--   Let $n>0$, $a_1,\ldots,a_n\in\mathbb C$, and $P=I-\mathbf1\mathbf1^*/n$. For $p(X)=\prod_i(X-a_i)$, $$\chi_{\operatorname{diag}(a)P}(X)=\frac{X}{n}p\prime(X).$$ The ambient matrix has the additional zero eigenvalue.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionCharpoly.lean#L9-L50

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.diagonal_projection_charpoly {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) :
    (diagonal a * centeringProjection n).charpoly =
      C (n : ℂ)⁻¹ * X * derivative (∏ i, (X-C (a i))) := by sorry
