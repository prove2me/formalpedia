-- Prove2me | Theorems.Thm_DerivativeChainPrivate_compressedPairCountRadius
-- name    : DerivativeChainPrivate.compressedPairCountRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T08:41:33.581258+00:00
-- url     : https://prove2.me/theorems/e0c21985-1992-4b34-9371-7c38d24fb0a1
-- title:
--   Compressed polynomials with K nonreal pairs have chain length at most (2K+1)R
-- statement:
--   Let n>=1, R>=0 and K be a natural number. Suppose every slot of a complex root list a has norm at most R, and its monic polynomial equals X^r Q(X^d), where d>=2, 0<=r<d and Q is a real polynomial with degree(Q)-cardinality(Q.roots over the reals)<=2K, counting multiplicities. There exists a complete chain selecting one actual root of every ordinary derivative row with length at most (2K+1)R. This includes K=0, R=0, repeated roots, arbitrary quotient degree and arbitrary symmetry order. The constant depends on K and does not settle either unrestricted prize question.
-- source:
--   Derivative-zero chains: public formalization reference, R54, DerivativeChainPrivate.compressedPairCountRadius. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.compressedPairCountRadius {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) (d r K : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hc : q.natDegree - q.roots.card ≤ 2 * K)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ (2 * (K : ℝ) + 1) * R := by sorry
