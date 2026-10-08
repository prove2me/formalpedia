-- Prove2me | Theorems.Thm_CompOT_Assignment_assignment_cost
-- name    : CompOT.Assignment.assignment_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:12.780411+00:00
-- url     : https://prove2.me/theorems/b7e05ef1-2565-485b-be06-9961d030d966
-- title:
--   §2.3, p. 372 — the cost of a scaled permutation coupling is the assignment objective
-- statement:
--   Let $n>0$, let $C$ be an $n\times n$ cost matrix, and let $\sigma$ be a permutation. The scaled permutation matrix $P_\sigma$ has transport cost equal to the assignment objective:
--
--   $$\langle C,P_\sigma\rangle=\frac1n\sum_{i=1}^{n} C_{i,\sigma(i)}=A_C(\sigma).$$
--
--   This identifies the objective of the combinatorial assignment problem with the linear objective used in its transport relaxation.
--
--   **Formalization Note** The condition $n>0$ excludes division by zero; `Fin n` indexes the same $n$ entries starting at zero.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §2.3, p. 372, display following (2.12)

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

theorem assignment_cost {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) :
    frob C (permCoupling σ) = assignmentCost C σ := by sorry

end CompOT.Assignment
