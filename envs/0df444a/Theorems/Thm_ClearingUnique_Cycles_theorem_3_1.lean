-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_theorem_3_1
-- name    : ClearingUnique.Cycles.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:58.541794+00:00
-- url     : https://prove2.me/theorems/f020eec4-7608-41af-9dc4-cd662017866d
-- title:
--   Theorem 3.1, p. 9 — clearing matrices solve the payment equations
-- statement:
--   Let $N=(I,z,L,d)$ be a financial network satisfying the standing assumptions, and let $P$ be a nonnegative payment matrix with zero diagonal. Then $P$ is a clearing payment matrix exactly when every entry is the payment prescribed at the agent's asset value:
--
--   $$
--   P_{ij}=d^i_j\bigl(a_i(P)\bigr)\qquad(i,j\in I).
--   $$
--
--   This theorem identifies the fixed points of the payment system with the economically defined clearing matrices of Definition 2.2.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 9 (PDF 11), Theorem 3.1

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem theorem_3_1 (N : FinNetwork I) (hN : N.Standing)
    (P : I → I → ℝ) (hP : InM P) :
    IsClearing N P ↔ ∀ i j, P i j = N.d i (assetValue N P i) j := by sorry

end ClearingUnique.Cycles
