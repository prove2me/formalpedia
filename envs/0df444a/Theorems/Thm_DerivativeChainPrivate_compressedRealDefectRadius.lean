-- Prove2me | Theorems.Thm_DerivativeChainPrivate_compressedRealDefectRadius
-- name    : DerivativeChainPrivate.compressedRealDefectRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T08:38:02.96684+00:00
-- url     : https://prove2.me/theorems/20a17491-d15d-4fd3-b116-128f0e08cf3b
-- title:
--   Real compressed chains have length at most root deficit plus one times the radius
-- statement:
--   Let n>=1, R>=0, and a be a list of n complex root slots of norm at most R. Suppose its monic polynomial is X^r Q(X^d), with d>=2, 0<=r<d and Q real. Let D=degree(Q)-cardinality(Q.roots over the reals), counting multiplicities. There exists a complete chain through every actual ordinary derivative row of length at most (D+1)R. The quotient degree, symmetry order, real-root multiplicities and radius are unrestricted. The case R=0 is included. This is a bound depending on the compressed nonreal-root deficit, not an unrestricted constant.
-- source:
--   Derivative-zero chains: public formalization reference, R53, DerivativeChainPrivate.compressedRealDefectRadius. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.compressedRealDefectRadius {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧
      chainCost z ≤ (1 + ((q.natDegree - q.roots.card : ℕ) : ℝ)) * R := by sorry
