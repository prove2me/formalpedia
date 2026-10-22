-- Prove2me | Theorems.Thm_EastinKnill_Transversal_finitely_many_actions
-- name    : EastinKnill.Transversal.finitely_many_actions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:49.497778+00:00
-- url     : https://prove2.me/theorems/1f3b754c-2627-492e-a044-9650d07fdeb6
-- title:
--   Proof of Theorem 1, p. 3 — $\mathcal G$ has finitely many actions on the code space, up to phase
-- statement:
--   Let $P$ be the projector of a local-error-detecting code on a composite system, and let $\mathcal G$ be the set of logical unitary product operators. Then there is a finite set $\mathcal F \subseteq \mathcal G$ such that every $G \in \mathcal G$ acts on the code space as some element of $\mathcal F$ up to a scalar: for every $G\in\mathcal G$ there are $F \in \mathcal F$ and $c\in\mathbb C$ with
--
--   $$G\,P = c\,F\,P.$$
--
--   In the paper $\mathcal F$ is a set of representatives of the cosets of the identity component $\mathcal C$ in $\mathcal G$; it is finite because the coset space is discrete and $\mathcal T$ is compact. So the logically distinct transversal operations are finitely many.
--
--   **Formalization Note** The page writes $GP = FCP = FP$. Because $C\in\mathcal C$ acts as a scalar and not necessarily as the identity (see the identity-component milestone), the faithful statement carries a scalar $c$.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, proof of Theorem 1, display "GP = FCP = FP" and the finiteness of ℱ

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem finitely_many_actions {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]
    (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) (hP : IsCodeProjector P)
    (hdet : IsLocalErrorDetecting P) :
    ∃ F : Finset (Matrix (∀ j, α j) (∀ j, α j) ℂ),
      (∀ V ∈ F, ∃ U ∈ logicalProductUnitaries α P, (U : Matrix (∀ j, α j) (∀ j, α j) ℂ) = V) ∧
      ∀ G ∈ logicalProductUnitaries α P,
        ∃ V ∈ F, ∃ c : ℂ, (G : Matrix (∀ j, α j) (∀ j, α j) ℂ) * P = c • (V * P) := by sorry

end EastinKnill.Transversal
