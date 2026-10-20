-- Prove2me | Theorems.Thm_DerivativeChainPrivate_compressedOnePairThreeRadius
-- name    : DerivativeChainPrivate.compressedOnePairThreeRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:32:46.817057+00:00
-- url     : https://prove2.me/theorems/674db3be-d028-4920-b313-01f5db9360f1
-- title:
--   Compressed one-pair chains have length at most three times the source radius
-- statement:
--   Let n be a positive integer, R>=0, and a a complex root list with every slot of norm at most R. Suppose its monic polynomial equals X^r Q(X^d), where d>=2, 0<=r<d, and Q is real with degree minus its number of real root slots at most two, counting multiplicities. There exists a complete chain through every actual ordinary derivative row with total length at most 3R. The symmetry order, quotient degree, real-root multiplicities and nonnegative radius are unrestricted. The case R=0 is included. This is the compressed one-pair class theorem, not either unrestricted prize question.
-- source:
--   Derivative-zero chains: public formalization reference, R52, DerivativeChainPrivate.compressedOnePairThreeRadius. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.compressedOnePairThreeRadius {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hc : q.natDegree - q.roots.card ≤ 2)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 3 * R := by sorry
