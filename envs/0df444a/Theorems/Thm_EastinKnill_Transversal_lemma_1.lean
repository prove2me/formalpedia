-- Prove2me | Theorems.Thm_EastinKnill_Transversal_lemma_1
-- name    : EastinKnill.Transversal.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:32.40352+00:00
-- url     : https://prove2.me/theorems/eadf80e9-3f6d-43ae-bd2e-a2814a0d7b63
-- title:
--   Lemma 1, p. 2 — the logical unitary operators form a group
-- statement:
--   Let $P$ be the projector onto the code space of a quantum code on a finite-dimensional system. A unitary $U$ is logical if $(I-P)UP = 0$ (Eq. (1)). Then the set
--
--   $$\mathcal L = \{\, U \text{ unitary} : (I-P)\,U\,P = 0 \,\}$$
--
--   is a subgroup of the unitary group: it contains the identity and is closed under products and inverses.
--
--   This is the first structural fact behind the Eastin–Knill theorem: composing logical gates produces nothing beyond the group they already form.
--
--   **Formalization Note** The statement asserts the existence of a subgroup of `Matrix.unitaryGroup` whose carrier is exactly $\mathcal L$.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 2, Lemma 1

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem lemma_1 {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : IsCodeProjector P) :
    ∃ L : Subgroup (Matrix.unitaryGroup n ℂ),
      (L : Set (Matrix.unitaryGroup n ℂ)) =
        {U : Matrix.unitaryGroup n ℂ | IsLogical P (U : Matrix n n ℂ)} := by sorry

end EastinKnill.Transversal
