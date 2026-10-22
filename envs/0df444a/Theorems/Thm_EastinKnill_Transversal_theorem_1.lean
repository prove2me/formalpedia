-- Prove2me | Theorems.Thm_EastinKnill_Transversal_theorem_1
-- name    : EastinKnill.Transversal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:38.221525+00:00
-- url     : https://prove2.me/theorems/a6b52d04-97ac-4431-914a-a2224ce43b07
-- title:
--   Theorem 1, p. 2 — for a nontrivial local-error-detecting code, the logical unitary product operators are not universal
-- statement:
--   Let $\mathcal Q$ be a composite quantum system of finitely many subsystems, and let $P$ be the projector onto the code space of a quantum code on $\mathcal Q$ such that
--
--   1. the code is local-error-detecting: $P(I\otimes E\otimes I)P \propto P$ for every operator $E$ on any single subsystem;
--   2. the code is nontrivial: its dimension $\operatorname{rank} P$ is at least $2$.
--
--   Let $\mathcal G$ be the set of logical unitary product operators $\bigotimes_j U_j$, those with $(I-P)\big(\bigotimes_j U_j\big)P = 0$. Then $\mathcal G$ is not universal: there is a unitary $W$ of the code space that is not a limit of actions $PGP$ with $G\in\mathcal G$,
--
--   $$\{\,W : PWP = W,\ W^\dagger W = WW^\dagger = P\,\} \not\subseteq \overline{\{\,PGP : G\in\mathcal G\,\}}.$$
--
--   This is the product-gate form of the Eastin–Knill theorem; Corollary 1 obtains the transversal form by applying it to the transversal parts of a block code.
--
--   **Formalization Note** "Nontrivial" is the paper's "dimension greater than one" (p. 4), stated as $2 \le \operatorname{rank} P$. At rank $1$ the conclusion fails, since global phases are in $\mathcal G$. The closure is in the standard topology of complex matrices.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 2, Theorem 1 (proof p. 3); p. 4 (nontrivial = dimension > 1)

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]
    (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) (hP : IsCodeProjector P)
    (hdet : IsLocalErrorDetecting P) (hnt : 2 ≤ P.rank) :
    ¬ IsUniversal P (logicalProductUnitaries α P) := by sorry

end EastinKnill.Transversal
