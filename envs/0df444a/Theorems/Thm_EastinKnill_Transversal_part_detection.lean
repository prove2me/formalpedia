-- Prove2me | Theorems.Thm_EastinKnill_Transversal_part_detection
-- name    : EastinKnill.Transversal.part_detection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:39.854273+00:00
-- url     : https://prove2.me/theorems/21bcd5c6-4ccb-4148-83a7-0b956b9adb12
-- title:
--   Proof of Corollary 1, p. 3 — a block code of local-error-detecting codes detects any error on a single transversal part
-- statement:
--   Consider code blocks $b \in \beta$, each consisting of subsystems at positions $j\in\iota$, with a code projector $P_b$ on each block that is local-error-detecting on that block's subsystems. Group the subsystems into transversal parts: part $j$ consists of subsystem $j$ of every block. Then the joint code $\bigotimes_b P_b$, viewed on the system of transversal parts, is local-error-detecting with respect to the parts: for every part $j$ and every operator $E$ on part $j$,
--
--   $$\Big(\bigotimes_b P_b\Big)\,(I\otimes E\otimes I)\,\Big(\bigotimes_b P_b\Big) \propto \bigotimes_b P_b.$$
--
--   This is the step of the proof of Corollary 1 that lets Theorem 1 be applied with the transversal parts in the role of the subsystems: an error on one transversal part is a single-subsystem error on each code block.
--
--   **Formalization Note** An operator $E$ on part $j$ is an arbitrary matrix on the tensor product of the $j$-th subsystems of all blocks, not necessarily a product operator.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, proof of Corollary 1

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem part_detection {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    {α : β → ι → Type*} [∀ b j, Fintype (α b j)] [∀ b j, DecidableEq (α b j)]
    (P : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ)
    (hP : ∀ b, IsCodeProjector (P b)) (hdet : ∀ b, IsLocalErrorDetecting (P b)) :
    IsLocalErrorDetecting (α := fun j => ∀ b, α b j) (blockCode α P) := by sorry

end EastinKnill.Transversal
