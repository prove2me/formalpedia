-- Prove2me | Theorems.Thm_DerivativeChainContinuation_exists_first_eigenvector_basis
-- name    : DerivativeChainContinuation.exists_first_eigenvector_basis
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:17:57.819324+00:00
-- url     : https://prove2.me/theorems/caaccbeb-f566-4383-815f-90735cbfb64e
-- title:
--   An orthonormal basis beginning with an eigenvector
-- statement:
--   Every complex square matrix of dimension $n+1$ has an orthonormal basis whose first vector is an eigenvector. Thus there are an eigenvalue $\mu$ and a basis $b$ with $$A b_0=\mu b_0.$$ This is a classical finite-dimensional linear algebra ingredient.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchurFirstVector.lean#L8-L31

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.exists_first_eigenvector_basis (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    ∃ (μ : ℂ) (b : OrthonormalBasis (Fin (n+1)) ℂ (EuclideanSpace ℂ (Fin (n+1)))),
      A.toEuclideanLin (b 0) = μ • b 0 := by sorry
