-- Prove2me | Theorems.Thm_DerivativeChainPrivate_compressedOnePairThree
-- name    : DerivativeChainPrivate.compressedOnePairThree
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:30:02.731233+00:00
-- url     : https://prove2.me/theorems/a64f451b-056e-46cd-b775-cbcf0c185839
-- title:
--   Compressed one-pair chains have length at most three
-- statement:
--   For every positive degree n and complex root list a in the closed unit disk, suppose its monic polynomial is X^r Q(X^d), with d>=2, 0<=r<d, and Q a real polynomial with degree minus the number of its real root slots at most two. Multiplicities are counted. Then there exists a complete chain selecting an actual root of every ordinary derivative row, with total length at most three. The quotient degree and symmetry order are unrestricted. This is the normalized one-pair compressed class theorem; it does not establish either unrestricted prize question.
-- source:
--   Derivative-zero chains: public formalization reference, R51, DerivativeChainPrivate.compressedOnePairThree. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.compressedOnePairThree {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (ha : ∀ i, ‖a i‖ ≤ 1) (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hc : q.natDegree - q.roots.card ≤ 2)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 3 := by sorry
