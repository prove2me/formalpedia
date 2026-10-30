-- Prove2me | Theorems.Thm_DerivativeChainContinuation_triangular_gram_product_lower
-- name    : DerivativeChainContinuation.triangular_gram_product_lower
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:26:41.689806+00:00
-- url     : https://prove2.me/theorems/dc466908-db4a-4ec5-b6d8-7ae4d9af41e1
-- title:
--   Diagonal spectral product lower bound for a triangular Gram determinant
-- statement:
--   For an upper triangular complex matrix $T$ and $t>0$, $$\prod_j(t+|T_{jj}|^2)\le|\det(tI+T^*T)|.$$ The statement includes dimension zero.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TriangularGramLower.lean#L9-L34

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder

theorem DerivativeChainContinuation.triangular_gram_product_lower (n : ℕ) (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsUpperTriangular) (t : ℝ) (ht : 0 < t) :
    (∏ j,(t+Complex.normSq (T j j))) ≤ ‖(regularizedGram T t).det‖ := by sorry
