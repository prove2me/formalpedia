-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_prop7_vi
-- name    : ExactSDPDuality.ELSD.prop7_vi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:12:19.469127+00:00
-- url     : https://prove2.me/theorems/869e9b45-0a8b-4963-8a38-003e14d92b0c
-- title:
--   Proposition 7(vi) — for PSD A, B: A • B = 0 iff AB = 0
-- statement:
--   Let $A, B$ be real $n\times n$ positive semidefinite matrices, and let $A\bullet B = \sum_{i,j}A_{ij}B_{ij}$. Then
--   $$A\bullet B = 0 \iff AB = 0 .$$
--
--   This is the fact that turns the scalar orthogonality conditions $Q^\#(\cdot) = 0$ defining the sets $\mathcal C_k$ into the matrix annihilation conditions of Lemma 9.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 139, Proposition 7(vi)

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Proposition 7(vi) (Ramana 1997, p. 139): for positive semidefinite `A, B`,
`A • B = 0` if and only if `AB = 0`. -/
theorem prop7_vi {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    frob A B = 0 ↔ A * B = 0 := by sorry

end ExactSDPDuality.ELSD
