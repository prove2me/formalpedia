-- Prove2me | Theorems.Thm_EastinKnill_Transversal_lemma_2
-- name    : EastinKnill.Transversal.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:37.931845+00:00
-- url     : https://prove2.me/theorems/734a0621-46dc-4133-ad17-02eef340bd42
-- title:
--   Lemma 2, p. 2 — the logical operators in a closed group of unitaries form a closed subgroup
-- statement:
--   Let $P$ be a code projector and $\mathcal L$ the group of logical unitaries, $(I-P)UP = 0$. Let $\mathcal A$ be a closed subgroup of the unitary group. Then
--
--   $$\mathcal B = \mathcal A \cap \mathcal L$$
--
--   is a subgroup of the unitary group and is topologically closed.
--
--   By Cartan's closed-subgroup theorem, this makes $\mathcal B$ a Lie subgroup of $\mathcal A$, which is how the paper states Lemma 2. It is applied with $\mathcal A = \mathcal T$, the product unitaries, to make the logical product unitaries $\mathcal G$ a Lie group.
--
--   **Formalization Note** The paper's "Lie group of unitary operators" is read as a closed subgroup of the unitary group, and the conclusion "Lie subgroup" as "closed subgroup": Cartan's theorem is not in Mathlib, and closedness is the only property the paper's proof establishes.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 2, Lemma 2 and its proof

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem lemma_2 {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : IsCodeProjector P) (A : Subgroup (Matrix.unitaryGroup n ℂ))
    (hA : IsClosed (A : Set (Matrix.unitaryGroup n ℂ))) :
    ∃ B : Subgroup (Matrix.unitaryGroup n ℂ),
      (B : Set (Matrix.unitaryGroup n ℂ)) =
        (A : Set (Matrix.unitaryGroup n ℂ)) ∩ {U | IsLogical P (U : Matrix n n ℂ)} ∧
      IsClosed (B : Set (Matrix.unitaryGroup n ℂ)) := by sorry

end EastinKnill.Transversal
