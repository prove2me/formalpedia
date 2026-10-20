-- Prove2me | Theorems.Thm_DerivativeChainPrivate_realCompressedRayChain
-- name    : DerivativeChainPrivate.realCompressedRayChain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T06:02:19.835282+00:00
-- url     : https://prove2.me/theorems/c86d7958-6839-474e-894d-bf42752efa3d
-- title:
--   Real-compressed ray chains have length at most one
-- statement:
--   For every positive degree and unit-disk complex root list, if its monic polynomial is X^r Q(X^k), with k at least two, 0 <= r < k, and Q a real polynomial splitting over the reals, there is a complete chain through the actual derivative rows of total length at most one. Repeated roots are allowed.
-- source:
--   Derivative-zero chains: public formalization reference, R40, DerivativeChainPrivate.realCompressedRayChain. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.realCompressedRayChain {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (ha : ∀ i, ‖a i‖ ≤ 1) (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits)
    (hp : fromRoots a = Polynomial.X ^ r *
      (q.map Complex.ofRealHom).comp (Polynomial.X ^ k)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 1 := by sorry
