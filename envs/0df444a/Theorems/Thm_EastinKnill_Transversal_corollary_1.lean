-- Prove2me | Theorems.Thm_EastinKnill_Transversal_corollary_1
-- name    : EastinKnill.Transversal.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:40.712605+00:00
-- url     : https://prove2.me/theorems/657ca162-16be-47fd-8660-7732c626f1aa
-- title:
--   Corollary 1, p. 3 — for a nontrivial local-error-detecting code, transversal logical unitaries are not universal
-- statement:
--   Consider a quantum code made of code blocks $b \in \beta$. Every block consists of physical subsystems at the same positions $j \in \iota$ (subsystem $j$ of block $b$ has dimension $d_{b,j}$), and carries a code with projector $P_b$, so that the code of the whole system is $P = \bigotimes_b P_b$. Assume
--
--   1. each block code is local-error-detecting: $P_b(I\otimes E\otimes I)P_b \propto P_b$ for every operator $E$ on any single subsystem of block $b$;
--   2. the code is nontrivial: $\operatorname{rank} P \ge 2$.
--
--   The transversal parts are the sets $\{(b,j) : b\in\beta\}$ of $j$-th subsystems; a transversal unitary is a product $\bigotimes_j U_j$ of unitaries $U_j$ each acting on one transversal part. Let $\mathcal G$ be the set of transversal unitaries that are logical, $(I-P)UP = 0$. Then $\mathcal G$ is not universal: some unitary $W$ of the code space is not a limit of actions $PUP$, $U\in\mathcal G$,
--
--   $$\{\,W : PWP = W,\ W^\dagger W = WW^\dagger = P\,\} \not\subseteq \overline{\{\,PUP : U\in\mathcal G\,\}}.$$
--
--   This is the Eastin–Knill theorem: no quantum code that detects an arbitrary error on any single physical subsystem admits a universal set of transversal encoded gates.
--
--   **Formalization Note** The page's "code blocks" are modelled as a tensor product of block codes $P_b$, all blocks having the same positions $j$ and possibly different codes and subsystem dimensions; this is the paper's requirement that errors in different blocks are detected independently. A single block ($|\beta| = 1$) gives back Theorem 1. "Nontrivial" is the joint code's dimension at least 2 (p. 4). Universality is approximation of every encoded unitary in the standard topology of complex matrices.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, Corollary 1 and its proof; p. 1 (code blocks, transversal partition, universality); p. 4 (nontrivial)

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem corollary_1 {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    {α : β → ι → Type*} [∀ b j, Fintype (α b j)] [∀ b j, DecidableEq (α b j)]
    (P : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ)
    (hP : ∀ b, IsCodeProjector (P b)) (hdet : ∀ b, IsLocalErrorDetecting (P b))
    (hnt : 2 ≤ (blockCode α P).rank) :
    ¬ IsUniversal (blockCode α P)
      (logicalProductUnitaries (fun j => ∀ b, α b j) (blockCode α P)) := by sorry

end EastinKnill.Transversal
