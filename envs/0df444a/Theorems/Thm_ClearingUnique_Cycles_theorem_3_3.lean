-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_theorem_3_3
-- name    : ClearingUnique.Cycles.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:02.990406+00:00
-- url     : https://prove2.me/theorems/07035d7e-2afd-41b2-8e0f-6c5a5fdcf37f
-- title:
--   Theorem 3.3, p. 11 — all clearing matrices yield the same equity
-- statement:
--   Let $P$ and $P'$ be any two clearing payment matrices of the same financial network $N$ satisfying the standing assumptions. Their agents' equity vectors agree:
--
--   $$
--   e_i(P)=e_i(P')\qquad\text{for every }i\in I.
--   $$
--
--   Payments may differ even though equity is fixed. This invariant is used to rule out differing rows in the later uniqueness theorem.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 11 (PDF 13), Theorem 3.3

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem theorem_3_3 (N : FinNetwork I) (hN : N.Standing)
    (P Q : I → I → ℝ) (hP : IsClearing N P) (hQ : IsClearing N Q) :
    ∀ i, equity N P i = equity N Q i := by sorry

end ClearingUnique.Cycles
